-- Prove2me | solution 1 for NoHair.kerrNewman_exterior_diamondCurveConfinement
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:53:58.637089+00:00
-- url     : https://prove2.me/submissions/3e516d33-bbda-4e16-8b8c-e50fa6655fe7

import Theorems.Thm_NoHair_kerrNewman_exterior_radialVelocityBound
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

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


private abbrev J := Icc (0:ℝ) 1
private def weight (m a e : ℝ) (z : E4) :=
  (ksRadius a z-kerrNewmanOuterRadius m a e)*Real.exp (-(z 0)/m)

private theorem monotone_from_deriv (f d : ℝ → ℝ) (hd : ∀ s, HasDerivAt f (d s) s)
    (h : ∀ s ∈ J, 0 ≤ d s) : MonotoneOn f J := by
  have hf : Differentiable ℝ f := fun s => (hd s).differentiableAt
  exact monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) 1) hf.continuous.continuousOn hf.differentiableOn
    (fun s hs => (hd s).deriv.symm ▸ h s (interior_subset hs))

private theorem curve_envelope (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T (D m a e) γ) :
    let w (s : ℝ) := weight m a e (γ s).val
    (∀ s ∈ J, ∀ i : Fin 4, |(γ s).val i-(γ 0).val i| ≤ |(γ 1).val 0-(γ 0).val 0|) ∧
    (∀ s ∈ J, min (w 0) (w 1) ≤ w s) ∧
    ∀ s ∈ J, 0 ≤ ((γ 1).val 0-(γ 0).val 0)*timeComponent (T (γ s)) ∧
      (w 1-w 0)*timeComponent (T (γ s)) ≤ 0 := by
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
  let o : ℝ := if 0 < v 0 0 then 1 else -1
  have ho : o=1 ∨ o= -1 := by unfold o; split <;> simp
  have h₀ : (0:ℝ) ∈ J := left_mem_Icc.mpr zero_le_one
  have h₁ : (1:ℝ) ∈ J := right_mem_Icc.mpr zero_le_one
  have hsign (s : ℝ) (hs : s ∈ J) : 0 < o*v s 0 := by
    have he := sign_on_interval (fun t => v t 0) hcont hne 0 s h₀ hs
    unfold o
    split_ifs with h
    · simpa using he.mp h
    · have hh : v s 0 < 0 := lt_of_le_of_ne (le_of_not_gt (fun h' => h (he.mpr h'))) (hne s hs)
      simpa using hh
  have hTsign (s : ℝ) (hs : s ∈ J) : 0 < o*timeComponent (T (γ s)) := by
    have h1 := hsign s hs
    have h2 := (hcone s hs).2
    rcases ho with h|h <;> rw [h] at h1 ⊢
    · simpa using pos_of_mul_pos_right h2 (by linarith : 0 ≤ v s 0)
    · have ht : timeComponent (T (γ s)) < 0 := by
        by_contra! ht
        exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (show v s 0 ≤ 0 by linarith) ht)) h2
      simpa using ht
  have hmag (s : ℝ) (hs : s ∈ J) : |v s 0| = o*v s 0 := by
    have hh := abs_of_pos (hsign s hs)
    rw [abs_mul] at hh
    rcases ho with h|h <;> simpa [h] using hh
  let b := kerrNewmanOuterRadius m a e
  let w (s : ℝ) := weight m a e (f s)
  let dv (s : ℝ) := fderiv ℝ (ksRadius a) (f s) (v s)
  let dw (s : ℝ) := Real.exp (-(f s 0)/m)*(dv s-(ksRadius a (f s)-b)*(v s 0)/m)
  have hdr (s : ℝ) : HasDerivAt (fun t => ksRadius a (f t)) (dv s) s := by
    have hv := ((hf.differentiable (by simp) s).hasFDerivAt).hasDerivAt
    rw [hd] at hv
    exact (ksRadius_differentiableAt a (f s) (γ s).property).hasFDerivAt.comp_hasDerivAt s hv
  have hdw (s : ℝ) : HasDerivAt w (dw s) s := by
    apply (((hdr s).sub_const b).mul (((hder 0 s).neg.div_const m).exp)).congr_deriv
    dsimp [dw]; ring
  have hwd (s : ℝ) (hs : s ∈ J) : o*dw s ≤ 0 := by
    have hvv := (hγ.2 s hs).2.2.1
    let A := matrixBilin (kerrNewmanMetric m a e (γ s).val)
    change A (v s) (v s) ≤ 0 at hvv
    have hvs : G m a e (γ s) (o • v s) (o • v s) ≤ 0 := by
      change A (o • v s) (o • v s) ≤ 0
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg o) hvv]
    have ht : 0 ≤ (o • v s) 0 := (hsign s hs).le
    have h := kerrNewman_exterior_radialVelocityBound m a e hp (γ s) (hγ.2 s hs).1 (o • v s) ht hvs
    rw [map_smul] at h
    change m*(o*dv s) ≤ (ksRadius a (f s)-b)*(o*v s 0) at h
    have hh : o*(dv s-(ksRadius a (f s)-b)*(v s 0)/m) ≤ 0 := by
      apply le_of_mul_le_mul_left (a := m) _ hp.1
      rw [mul_zero]
      field_simp [hp.1.ne']
      nlinarith only [mul_le_mul_of_nonneg_left h hp.1.le, h]
    calc
      o*dw s = Real.exp (-(f s 0)/m)*(o*(dv s-(ksRadius a (f s)-b)*(v s 0)/m)) := by dsimp [dw]; ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hh
  have hwmono : MonotoneOn (fun s => -(o*w s)) J :=
    monotone_from_deriv _ _ (fun s => ((hdw s).const_mul o).neg) (fun s hs => neg_nonneg.mpr (hwd s hs))
  have htmono : MonotoneOn (fun s => o*f s 0) J :=
    monotone_from_deriv _ _ (fun s => (hder 0 s).const_mul o) (fun s hs => (hsign s hs).le)
  have ht01 := htmono h₀ h₁ zero_le_one
  have hw01 := hwmono h₀ h₁ zero_le_one
  change o*f 0 0 ≤ o*f 1 0 at ht01
  change -(o*w 0) ≤ -(o*w 1) at hw01
  have hclock : o*(f 1 0-f 0 0) = |f 1 0-f 0 0| := by
    rcases ho with h|h <;> rw [h] at ht01 ⊢
    · rw [abs_of_nonneg (by linarith : 0 ≤ f 1 0-f 0 0)]; ring
    · rw [abs_of_nonpos (by linarith : f 1 0-f 0 0 ≤ 0)]; ring
  refine ⟨?_,?_,?_⟩
  · intro s hs i
    have hplus : MonotoneOn (fun s => o*f s 0+f s i) J :=
      monotone_from_deriv _ _ (fun s => ((hder 0 s).const_mul o).add (hder i s)) (fun s hs => by
        have h := (hcone s hs).1 i
        rw [hmag s hs] at h
        linarith [neg_abs_le (v s i)])
    have hminus : MonotoneOn (fun s => o*f s 0-f s i) J :=
      monotone_from_deriv _ _ (fun s => ((hder 0 s).const_mul o).sub (hder i s)) (fun s hs => by
        have h := (hcone s hs).1 i
        rw [hmag s hs] at h
        linarith [le_abs_self (v s i)])
    have ha := hplus h₀ hs hs.1
    have hb := hminus h₀ hs hs.1
    have hc := htmono hs h₁ hs.2
    beta_reduce at ha hb hc
    change |f s i-f 0 i| ≤ |f 1 0-f 0 0|
    rw [← hclock]
    exact abs_le.mpr ⟨by nlinarith only [ha,hc],by nlinarith only [hb,hc]⟩
  · intro s hs
    have ha := hwmono h₀ hs hs.1
    have hb := hwmono hs h₁ hs.2
    beta_reduce at ha hb
    change min (w 0) (w 1) ≤ w s
    rcases ho with h|h <;> rw [h] at ha hb
    · exact (min_le_right _ _).trans (by linarith)
    · exact (min_le_left _ _).trans (by linarith)
  · intro s hs
    have hO := hTsign s hs
    change 0 ≤ (f 1 0-f 0 0)*timeComponent (T (γ s)) ∧ (w 1-w 0)*timeComponent (T (γ s)) ≤ 0
    rcases ho with h|h <;> rw [h] at hO ht01 hw01
    · exact ⟨mul_nonneg (by linarith) (by linarith),mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)⟩
    · exact ⟨mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith),
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)⟩

private theorem future_envelope (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) (p q : U a) (hpD : p ∈ D m a e)
    (hq : q ∈ causalFuture (G m a e) T (D m a e) p) :
    let w (x : U a) := weight m a e x.val
    let dt := q.val 0-p.val 0
    q ∈ D m a e ∧ (∀ i : Fin 4, |q.val i-p.val i| ≤ |dt|) ∧
      (0 ≤ dt*timeComponent (T p) ∧ (w q-w p)*timeComponent (T p) ≤ 0) ∧
      (0 ≤ dt*timeComponent (T q) ∧ (w q-w p)*timeComponent (T q) ≤ 0) ∧
      ∀ K : Set (U a), (∀ y : U a, min (w p) (w q) ≤ w y →
        (∀ i : Fin 4, |y.val i-p.val i| ≤ |dt|) → y∈K) →
          q ∈ causalFuture (G m a e) T K p := by
  rcases hq with he|⟨γ,hγ,hp',hq'⟩
  · rcases Set.mem_singleton_iff.mp he with rfl
    refine ⟨hpD, by simp, by simp, by simp, fun K _ => Or.inl rfl⟩
  · subst p
    subst q
    obtain ⟨hc,hw,ht⟩ := curve_envelope m a e hp T hT γ hγ
    have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
    have h₁ : (1:ℝ)∈J := right_mem_Icc.mpr zero_le_one
    refine ⟨(hγ.2 1 h₁).1, hc 1 h₁, ht 0 h₀, ht 1 h₁, ?_⟩
    intro K hK
    refine Or.inr ⟨γ,⟨hγ.1,?_⟩,rfl,rfl⟩
    intro s hs
    exact ⟨hK _ (hw s hs) (hc s hs),(hγ.2 s hs).2⟩

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
    let U := kerrNewmanSpacetime a
    let g := kerrNewmanMetricField m a e
    let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m a e
    ∀ p ∈ D, ∀ q ∈ D, ∃ K : Set U, IsCompact K ∧ K ⊆ D ∧ p ∈ K ∧ q ∈ K ∧
      ∀ x ∈ causalFuture g T D p ∩ causalPast g T D q,
        x ∈ K ∧ x ∈ causalFuture g T K p ∧ q ∈ causalFuture g T K x := by
  dsimp only
  intro p hpD q hqD
  let w := weight m a e
  let l := min (w p.val) (w q.val)
  let B := |q.val 0-p.val 0|
  let C (i : Fin 4) := |q.val i-p.val i|+2*B+1
  let box : Set (Fin 4 → ℝ) := Icc (fun i => p.val i-C i) (fun i => p.val i+C i)
  let H : Set E4 := (WithLp.toLp 2 '' box) ∩ {z | l ≤ w z}
  let K := (Subtype.val : U a → E4) ⁻¹' H
  have hB : 0 ≤ B := abs_nonneg _
  have hC (i : Fin 4) : 2*B ≤ C i := by dsimp [C]; linarith [abs_nonneg (q.val i-p.val i)]
  have hW : Continuous w := by
    unfold w weight
    exact ((continuous_ksRadius a).sub continuous_const).mul (by fun_prop)
  have hH : IsCompact H := ((show IsCompact box from isCompact_Icc).image (PiLp.continuous_toLp 2 _)).inter_right
    (isClosed_le continuous_const hW)
  have hweight (z : U a) (hz : z∈D m a e) : 0 < w z.val :=
    mul_pos (sub_pos.mpr hz) (Real.exp_pos _)
  have hl : 0<l := lt_min (hweight p hpD) (hweight q hqD)
  have hreg (z : E4) (hz : z ∈ H) : kerrNewmanOuterRadius m a e < ksRadius a z := by
    have hw := hl.trans_le hz.2
    change 0 < (ksRadius a z-kerrNewmanOuterRadius m a e)*Real.exp (-(z 0)/m) at hw
    by_contra! h
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (Real.exp_pos _).le)) hw
  have hb : 0<kerrNewmanOuterRadius m a e := hp.1.trans_le (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hcompact : IsCompact K := by
    apply Subtype.isCompact_iff.mpr
    have himg : (Subtype.val : U a → E4) '' K = H := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩; exact hx
      · intro hz
        exact ⟨⟨z,hb.trans (hreg z hz)⟩,hz,rfl⟩
    rwa [himg]
  have put (x : U a) (hw : l ≤ w x.val) (h : ∀ i : Fin 4, |x.val i-p.val i| ≤ C i) : x∈K := by
    refine ⟨⟨WithLp.ofLp x.val,⟨?_,?_⟩,rfl⟩,hw⟩
    · intro i; have ha := (abs_le.mp (h i)).1; change p.val i-C i ≤ x.val i; linarith
    · intro i; have ha := (abs_le.mp (h i)).2; change x.val i ≤ p.val i+C i; linarith
  have hpK := put p (min_le_left _ _) (fun i => by simp only [sub_self,abs_zero]; linarith [hC i])
  have hqK := put q (min_le_right _ _) (fun i => by dsimp [C]; linarith)
  refine ⟨K,hcompact,fun x hx => hreg x.val hx,hpK,hqK,?_⟩
  intro x hx
  obtain ⟨hxD,hxp,_,h1,hleg1⟩ := future_envelope m a e hp T hT p x hpD hx.1
  obtain ⟨_,_,h2,_,hleg2⟩ := future_envelope m a e hp T hT x q hxD hx.2
  let s := timeComponent (T x)
  have hs : s ≠ 0 := fun h =>
    (not_lt_of_ge (spatial_kernel m a e x (exterior_profile m a e hp x hxD) (T x) h)) (hT.2 x)
  have hxpT : |x.val 0-p.val 0| ≤ B := interval_length _ _ _ s hs h1.1 h2.1
  have hxqT : |q.val 0-x.val 0| ≤ B := by
    rw [abs_sub_comm,show B = |p.val 0-q.val 0| from abs_sub_comm _ _]
    apply interval_length _ _ _ (-s) (neg_ne_zero.mpr hs)
    · nlinarith only [h2.1]
    · nlinarith only [h1.1]
  have hxw : l ≤ w x.val := by
    have hA : (w x.val-w p.val)*s ≤ 0 := h1.2
    have hB' : (w q.val-w x.val)*s ≤ 0 := h2.2
    rcases lt_or_gt_of_ne hs with hn|hpos
    · apply (min_le_left _ _).trans
      by_contra! he
      exact (not_lt_of_ge hA) (mul_pos_of_neg_of_neg (sub_neg.mpr he) hn)
    · apply (min_le_right _ _).trans
      by_contra! he
      exact (not_lt_of_ge hB') (mul_pos (sub_pos.mpr he) hpos)
  have hxi (i : Fin 4) : |x.val i-p.val i| ≤ B := (hxp i).trans hxpT
  refine ⟨put x hxw (fun i => (hxi i).trans (by linarith [hC i])),hleg1 K ?_,hleg2 K ?_⟩
  · intro y hwy hy
    apply put y ((le_min (min_le_left _ _) hxw).trans hwy)
    exact fun i => (hy i).trans (hxpT.trans (by linarith [hC i]))
  · intro y hwy hy
    apply put y ((le_min hxw (min_le_right _ _)).trans hwy)
    intro i
    have htri : |y.val i-p.val i| ≤ |y.val i-x.val i|+|x.val i-p.val i| := by
      simpa only [Real.dist_eq] using dist_triangle (y.val i) (x.val i) (p.val i)
    linarith only [htri,(hy i).trans hxqT,hxi i,hC i]
