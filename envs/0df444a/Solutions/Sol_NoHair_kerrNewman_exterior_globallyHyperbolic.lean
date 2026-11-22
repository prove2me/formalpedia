-- Prove2me | solution 1 for NoHair.kerrNewman_exterior_globallyHyperbolic
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:23:25.155548+00:00
-- url     : https://prove2.me/submissions/c3b10f05-0f9b-44dc-b192-9ab2457637e7

import Theorems.Thm_NoHair_kerrNewman_exterior_causalDiamonds_closed

open NoHair Set
open scoped ContDiff Manifold BigOperators

noncomputable section

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev D (m a e : ℝ) := (Subtype.val : U a → E4) ⁻¹' kerrNewmanDOC m a e
private abbrev I4 := 𝓘(ℝ, E4)
private abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private def timeComponent (v : E4) : ℝ := v 0
private def kEval (a : ℝ) (z u : E4) := ∑ i, ksNull a z i * u i

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e x.val * kEval a x.val v * kEval a x.val w := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, kEval, Fin.sum_univ_four]
  simp [minkowski] <;> ring

private theorem exterior_profile (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : x ∈ D m a e) : 0 ≤ ksProfile m a e x.val := by
  obtain ⟨hm, he⟩ := hp
  change m + Real.sqrt (m^2 - a^2 - e^2) < ksRadius a x.val at hx
  have hm' : m ≤ ksRadius a x.val := by linarith [Real.sqrt_nonneg (m^2-a^2-e^2)]
  have hnum : 0 ≤ 2*m*ksRadius a x.val - e^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hm' hm.le, he, sq_nonneg a, sq_nonneg m]
  unfold ksProfile
  exact div_nonneg (mul_nonneg (sq_nonneg _) hnum) (by positivity)

private theorem spatial_squares (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (hv : G m a e x v v ≤ 0) :
    (v 1)^2 + (v 2)^2 + (v 3)^2 ≤ (v 0)^2 := by
  rw [metric_formula] at hv
  nlinarith only [hv, mul_nonneg hf (sq_nonneg (kEval a x.val v))]

private theorem spatial_kernel (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (h0 : v 0 = 0) : 0 ≤ G m a e x v v := by
  rw [metric_formula, h0]
  nlinarith only [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3),
    mul_nonneg hf (sq_nonneg (kEval a x.val v))]

private theorem cone_estimates (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v w : E4) (hv : v ≠ 0) (hvv : G m a e x v v ≤ 0) (hvw : G m a e x v w < 0)
    (hww : G m a e x w w < 0) :
    (∀ i, |v i| ≤ |v 0|) ∧ 0 < (v 0)*(w 0) := by
  have hs := spatial_squares m a e x hf v hvv
  have hb (i : Fin 4) : |v i| ≤ |v 0| := by
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs, sq_abs]
    fin_cases i <;> simp <;> nlinarith only [hs, sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have hv0 : v 0 ≠ 0 := by
    intro h
    apply hv
    ext i
    exact abs_nonpos_iff.mp (by simpa only [h, abs_zero] using hb i)
  refine ⟨hb, ?_⟩
  by_contra! hprod
  have hkernel := spatial_kernel m a e x hf ((w 0) • v - (v 0) • w)
    (by simp [smul_eq_mul, mul_comm])
  have hsym : G m a e x w v = G m a e x v w := by rw [metric_formula, metric_formula]; ring
  let A := matrixBilin (kerrNewmanMetric m a e x.val)
  change 0 ≤ A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hkernel
  change A w v = A v w at hsym
  change A w w < 0 at hww
  change A v v ≤ 0 at hvv
  change A v w < 0 at hvw
  simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hsym] at hkernel
  nlinarith only [hkernel, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hvv,
    mul_neg_of_pos_of_neg (sq_pos_iff.mpr hv0) hww, mul_nonneg_of_nonpos_of_nonpos hprod hvw.le]

private theorem sign_on_interval (f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ 0) (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < f u ↔ 0 < f v := by
  have imp (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hp : 0 < f s) :
      0 < f t := by
    by_contra! h
    obtain ⟨z, hz, he⟩ := isPreconnected_Icc.intermediate_value ht hs hf.continuousOn
      (show (0:ℝ) ∈ Icc (f t) (f s) from ⟨h,hp.le⟩)
    exact hn z hz he
  exact ⟨imp u v hu hv, imp v u hv hu⟩

private theorem curve_estimates (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T (D m a e) γ) :
    (∀ i : Fin 4, |(γ 1).val i - (γ 0).val i| ≤ |(γ 1).val 0 - (γ 0).val 0|) ∧
    ∀ t ∈ Icc (0:ℝ) 1, 0 < ((γ 1).val 0 - (γ 0).val 0) * timeComponent (T (γ t)) := by
  let f : ℝ → E4 := Subtype.val ∘ γ
  let v (t : ℝ) : E4 := velocity γ t
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hf : ContDiff ℝ 1 f := (hval.comp hγ.1).contDiff
  have hd (t : ℝ) : fderiv ℝ f t = (mfderiv 𝓘(ℝ, ℝ) I4 γ t : ℝ →L[ℝ] E4) := by
    have h := mfderiv_comp t (hval.mdifferentiableAt (by simp) (x := γ t)) (hγ.1.mdifferentiableAt (by simp))
    have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ t) : E4 →L[ℝ] E4) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ t)
    rw [hinc] at h
    rw [← mfderiv_eq_fderiv]
    exact h
  have hc (i : Fin 4) : ContDiff ℝ 1 (fun t => f t i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hf
  have hder (i : Fin 4) (t : ℝ) : HasDerivAt (fun s => f s i) (v t i) t := by
    have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp t ((hf.differentiable (by simp) t).hasFDerivAt)).hasDerivAt
    rw [hd] at h
    exact h
  have hcone (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (∀ i, |v t i| ≤ |v t 0|) ∧ 0 < (v t 0) * timeComponent (T (γ t)) := by
    obtain ⟨hx,hne,hvv,hvw⟩ := hγ.2 t ht
    exact cone_estimates m a e (γ t) (exterior_profile m a e hp _ hx)
      (v t) (T (γ t)) hne hvv hvw (hT.2 _)
  have hne (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : v t 0 ≠ 0 := by
    have h := (hcone t ht).2
    intro he
    rw [he, zero_mul] at h
    exact (lt_irrefl _) h
  have hcont : Continuous (fun t => v t 0) := by
    have he : (fun t => v t 0) = deriv (fun t => f t 0) := funext (fun t => (hder 0 t).deriv.symm)
    rw [he]
    exact (hc 0).continuous_deriv le_rfl
  constructor
  · intro i
    obtain ⟨c, hc', he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
      (fun t => f t 0) (fun t => v t 0) zero_lt_one (hc 0).continuous.continuousOn (fun t _ => hder 0 t)
      (fun t => f t i) (fun t => v t i) (hc i).continuous.continuousOn (fun t _ => hder i t)
    have hci := Ioo_subset_Icc_self hc'
    have h := congrArg abs he
    simp only [abs_mul] at h
    apply le_of_mul_le_mul_right (a := |v c 0|) _ (abs_pos.mpr (hne c hci))
    exact h.trans_le (mul_le_mul_of_nonneg_left ((hcone c hci).1 i) (abs_nonneg _))
  · intro t ht
    obtain ⟨c,hc',he⟩ := exists_hasDerivAt_eq_slope (fun s => f s 0) (fun s => v s 0) zero_lt_one
      (hc 0).continuous.continuousOn (fun s _ => hder 0 s)
    simp only [sub_zero, div_one] at he
    change 0 < (f 1 0 - f 0 0) * _
    rw [← he]
    have hci := Ioo_subset_Icc_self hc'
    have hsign := sign_on_interval (fun s => v s 0) hcont hne c t hci ht
    rcases (mul_pos_iff.mp (hcone t ht).2) with h|h
    · exact mul_pos (hsign.mpr h.1) h.2
    · have hneg : v c 0 < 0 := lt_of_le_of_ne (le_of_not_gt (fun hh => h.1.not_gt (hsign.mp hh))) (hne c hci)
      exact mul_pos_of_neg_of_neg hneg h.2

private theorem future_bounds (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) (p q : U a) (hpD : p ∈ D m a e)
    (hq : q ∈ causalFuture (G m a e) T (D m a e) p) :
    q ∈ D m a e ∧ (∀ i : Fin 4, |q.val i - p.val i| ≤ |q.val 0-p.val 0|) ∧
      0 ≤ (q.val 0-p.val 0) * (timeComponent (T p)) ∧ 0 ≤ (q.val 0-p.val 0) * (timeComponent (T q)) := by
  rcases hq with he|⟨γ,hγ,hp',hq'⟩
  · rcases Set.mem_singleton_iff.mp he with rfl
    simp [hpD]
  · obtain ⟨hb, ht⟩ := curve_estimates m a e hp T hT γ hγ
    have h0 := ht 0 (left_mem_Icc.mpr zero_le_one)
    have h1 := ht 1 (right_mem_Icc.mpr zero_le_one)
    have hD := (hγ.2 1 (right_mem_Icc.mpr zero_le_one)).1
    rw [hp',hq'] at hb h0 h1
    exact ⟨hq' ▸ hD, hb, h0.le, h1.le⟩

private theorem interval_length (u v w s : ℝ) (hs : s ≠ 0)
    (h1 : 0 ≤ (v-u)*s) (h2 : 0 ≤ (w-v)*s) : |v-u| ≤ |w-u| := by
  rcases lt_or_gt_of_ne hs with hn|hp
  · have hv : v-u ≤ 0 := by by_contra! h; exact (not_lt_of_ge h1) (mul_neg_of_pos_of_neg h hn)
    have hw : w-v ≤ 0 := by by_contra! h; exact (not_lt_of_ge h2) (mul_neg_of_pos_of_neg h hn)
    rw [abs_of_nonpos hv, abs_of_nonpos (by linarith : w-u ≤ 0)]
    linarith
  · have hv : 0 ≤ v-u := by by_contra! h; exact (not_lt_of_ge h1) (mul_neg_of_neg_of_pos h hp)
    have hw : 0 ≤ w-v := by by_contra! h; exact (not_lt_of_ge h2) (mul_neg_of_neg_of_pos h hp)
    rw [abs_of_nonneg hv, abs_of_nonneg (by linarith : 0 ≤ w-u)]
    linarith

theorem solution (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    IsGloballyHyperbolicOn (kerrNewmanMetricField m a e) T
      ((Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a e) := by
  constructor
  · intro p hpD
    rintro ⟨γ,hγ,h0,h1⟩
    have h := (curve_estimates m a e hp T hT γ hγ).2 0 (left_mem_Icc.mpr zero_le_one)
    simp [h0,h1] at h
  · intro p hpD q hqD
    let E := causalFuture (G m a e) T (D m a e) p ∩ causalPast (G m a e) T (D m a e) q
    let B := |q.val 0-p.val 0|
    let K : Set (Fin 4 → ℝ) := Icc (fun i => p.val i-B) (fun i => p.val i+B)
    have hK : IsCompact K := isCompact_Icc
    have hClosed := kerrNewman_exterior_causalDiamonds_closed m a e hp T hT p hpD q hqD
    apply Subtype.isCompact_iff.mpr
    apply (hK.image (PiLp.continuous_toLp 2 _)).of_isClosed_subset hClosed
    rintro z ⟨x, hx, rfl⟩
    change x ∈ E at hx
    obtain ⟨hxD,hxp,_,hsx⟩ := future_bounds m a e hp T hT p x hpD hx.1
    obtain ⟨_,_,hxq,_⟩ := future_bounds m a e hp T hT x q hxD hx.2
    have hs : (timeComponent (T x)) ≠ 0 := fun h =>
      (not_lt_of_ge (spatial_kernel m a e x (exterior_profile m a e hp x hxD) (T x) h)) (hT.2 x)
    have ht := interval_length (p.val 0) (x.val 0) (q.val 0) (timeComponent (T x)) hs hsx hxq
    have hbox (i : Fin 4) := abs_le.mp ((hxp i).trans ht)
    exact ⟨WithLp.ofLp x.val, ⟨fun i => by have h := (hbox i).1; change p.val i - B ≤ x.val i; dsimp [B]; linarith,
      fun i => by have h := (hbox i).2; change x.val i ≤ p.val i + B; dsimp [B]; linarith⟩, rfl⟩
