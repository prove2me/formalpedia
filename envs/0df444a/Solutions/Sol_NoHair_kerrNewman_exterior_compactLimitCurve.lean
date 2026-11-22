-- Prove2me | solution 1 for NoHair.kerrNewman_exterior_compactLimitCurve
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:58:22.729792+00:00
-- url     : https://prove2.me/submissions/851c3d90-d0e0-45dd-b303-5ca74ec35df7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_kerrNewman_exterior_localCausalClosure
import Theorems.Thm_NoHair_kerrNewman_exterior_causalTransitivity

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
private theorem monotone_from_deriv (f d : ℝ → ℝ) (hd : ∀ s, HasDerivAt f (d s) s)
    (h : ∀ s ∈ J, 0 ≤ d s) : MonotoneOn f J := by
  have hf : Differentiable ℝ f := fun s => (hd s).differentiableAt
  exact monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) 1) hf.continuous.continuousOn hf.differentiableOn
    (fun s hs => (hd s).deriv.symm ▸ h s (interior_subset hs))


private theorem arc_displacement (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T (D m a e) γ) (s : ℝ) (hs : s∈J) :
    dist (γ s) (γ 0) ≤ 2*|(γ 1).val 0-(γ 0).val 0| := by
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
  have hmag (s : ℝ) (hs : s ∈ J) : |v s 0| = o*v s 0 := by
    have hh := abs_of_pos (hsign s hs)
    rw [abs_mul] at hh
    rcases ho with h|h <;> simpa [h] using hh
  have htmono : MonotoneOn (fun s => o*f s 0) J :=
    monotone_from_deriv _ _ (fun s => (hder 0 s).const_mul o) (fun s hs => (hsign s hs).le)
  have ht01 := htmono h₀ h₁ zero_le_one
  change o*f 0 0 ≤ o*f 1 0 at ht01
  have hclock : o*(f 1 0-f 0 0) = |f 1 0-f 0 0| := by
    rcases ho with h|h <;> rw [h] at ht01 ⊢
    · rw [abs_of_nonneg (by linarith : 0 ≤ f 1 0-f 0 0)]; ring
    · rw [abs_of_nonpos (by linarith : f 1 0-f 0 0 ≤ 0)]; ring
  have hcoords (i : Fin 4) : |f s i-f 0 i| ≤ |f 1 0-f 0 0| := by
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
  let B := |f 1 0-f 0 0|
  have hb : 0 ≤ B := abs_nonneg _
  have hsq (i : Fin 4) : (f s i-f 0 i)^2 ≤ B^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr (hcoords i)
  change ‖f s-f 0‖ ≤ 2*B
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  change (f s 0-f 0 0)^2+(f s 1-f 0 1)^2+(f s 2-f 0 2)^2+(f s 3-f 0 3)^2 ≤ _
  nlinarith only [hsq 0,hsq 1,hsq 2,hsq 3]

private theorem restrict_arc (m a e : ℝ) (T : VecField (U a)) (K : Set (U a)) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T K γ) (l h : ℝ) (hl : 0≤l) (hh : 0<h) (hlh : l+h≤1) :
    IsFutureCausalCurveIn (G m a e) T K (fun s => γ (l+h*s)) := by
  let φ (s : ℝ) := l+h*s
  have hφ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) 1 φ := contMDiff_iff_contDiff.mpr (by dsimp [φ]; fun_prop)
  refine ⟨hγ.1.comp hφ,?_⟩
  intro s hs
  have hi : φ s ∈ J := ⟨by dsimp [φ]; linarith [mul_nonneg hh.le hs.1],by dsimp [φ]; nlinarith only [hlh,mul_le_mul_of_nonneg_left hs.2 hh.le]⟩
  obtain ⟨hK,hn,hvv,hvT⟩ := hγ.2 (φ s) hi
  have dφ : HasDerivAt φ h s := by simpa [φ] using (((hasDerivAt_id s).const_mul h).const_add l)
  have hvel : (velocity (γ ∘ φ) s : E4) = h • (velocity γ (φ s) : E4) := by
    unfold velocity
    rw [mfderiv_comp s (hγ.1.mdifferentiableAt (by simp)) (hφ.mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
    change mfderiv 𝓘(ℝ,ℝ) I4 γ (φ s) (fderiv ℝ φ s 1) = _
    rw [show fderiv ℝ φ s 1 = h from dφ.deriv]
    let L : ℝ →L[ℝ] E4 := mfderiv 𝓘(ℝ,ℝ) I4 γ (φ s)
    change L h = h • L 1
    simpa only [smul_eq_mul,mul_one] using L.map_smul h (1:ℝ)
  let A := matrixBilin (kerrNewmanMetric m a e (γ (φ s)).val)
  let v : E4 := velocity γ (φ s)
  let w : E4 := T (γ (φ s))
  change v ≠ 0 at hn
  change A v v ≤ 0 at hvv
  change A v w < 0 at hvT
  refine ⟨hK,?_⟩
  change (velocity (γ ∘ φ) s : E4) ≠ 0 ∧ A (velocity (γ ∘ φ) s) (velocity (γ ∘ φ) s) ≤ 0 ∧
    A (velocity (γ ∘ φ) s) w<0
  rw [hvel]
  change (h • v : E4) ≠ 0 ∧ A (h • v) (h • v) ≤ 0 ∧ A (h • v) w < 0
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  exact ⟨smul_ne_zero hh.ne' hn,mul_nonpos_of_nonneg_of_nonpos hh.le (mul_nonpos_of_nonneg_of_nonpos hh.le hvv),
    mul_neg_of_pos_of_neg hh hvT⟩

private def composeRel {X : Type*} (A : Set (X × X)) : Set (X × X) := {z | ∃ x, (z.1,x)∈A ∧ (x,z.2)∈A}

private theorem compact_composition {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set (X × X)}
    (hA : IsCompact A) : IsCompact (composeRel A) := by
  let S : Set ((X×X)×(X×X)) := {z | z.1.2=z.2.1}
  have hs : IsClosed S := isClosed_eq (continuous_snd.comp continuous_fst) (continuous_fst.comp continuous_snd)
  let F (z : (X×X)×(X×X)) := (z.1.1,z.2.2)
  have e : composeRel A = F '' ((A ×ˢ A) ∩ S) := by
    ext z
    constructor
    · rintro ⟨x,h1,h2⟩
      exact ⟨((z.1,x),(x,z.2)),⟨⟨h1,h2⟩,rfl⟩,rfl⟩
    · rintro ⟨⟨⟨p,x⟩,⟨y,q⟩⟩,⟨⟨hx,hy⟩,h⟩,rfl⟩
      change x=y at h
      subst y
      exact ⟨x,hx,hy⟩
  rw [e]
  exact ((hA.prod hA).inter_right hs).image ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))

private def shortRel (m a e : ℝ) (T : VecField (U a)) (K : Set (U a)) (d : ℝ) : Set (U a × U a) :=
  {z | z.1∈K ∧ z.2∈K ∧ z.2∈causalFuture (G m a e) T K z.1 ∧ |z.2.val 0-z.1.val 0|≤d}

private theorem bisect (m a e : ℝ) (T : VecField (U a)) (K : Set (U a)) (d : ℝ) (hd : 0≤d) :
    shortRel m a e T K (2*d) ⊆ composeRel (shortRel m a e T K d) := by
  rintro ⟨p,q⟩ ⟨hp,hq,hj,hlen⟩
  by_cases hshort : |q.val 0-p.val 0|≤d
  · exact ⟨p,⟨hp,hp,Or.inl rfl,by simpa⟩,⟨hp,hq,hj,hshort⟩⟩
  rcases hj with he|⟨γ,hγ,h0,h1⟩
  · have hqp : q = p := Set.mem_singleton_iff.mp he
    exact (hshort (by simpa [hqp] using hd)).elim
  let t (s : ℝ) := (γ s).val 0
  have hc : Continuous t := (PiLp.continuous_apply 2 _ 0).comp (continuous_subtype_val.comp hγ.1.continuous)
  have hne : t 0 ≠ t 1 := by
    intro h
    change (γ 0).val 0 = (γ 1).val 0 at h
    rw [h0,h1] at h
    change p.val 0 = q.val 0 at h
    exact hshort (by rw [h,sub_self,abs_zero]; exact hd)
  let mid := (t 0+t 1)/2
  have hmid : mid ∈ t '' J := by
    rcases le_total (t 0) (t 1) with h|h
    · apply intermediate_value_Icc zero_le_one hc.continuousOn
      exact ⟨by dsimp [mid]; linarith,by dsimp [mid]; linarith⟩
    · apply intermediate_value_Icc' zero_le_one hc.continuousOn
      exact ⟨by dsimp [mid]; linarith,by dsimp [mid]; linarith⟩
  obtain ⟨s,hs,he⟩ := hmid
  have hs0 : 0<s := lt_of_le_of_ne hs.1 (fun h => by
    subst s; dsimp [mid] at he; apply hne; linarith)
  have hs1 : s<1 := lt_of_le_of_ne hs.2 (fun h => by
    subst s; dsimp [mid] at he; apply hne; linarith)
  have hsK := (hγ.2 s hs).1
  have hγa := restrict_arc m a e T K γ hγ 0 s le_rfl hs0 (by linarith)
  have hγb := restrict_arc m a e T K γ hγ s (1-s) hs.1 (by linarith) (by linarith)
  have hpq : |t 1-t 0| ≤ 2*d := by simpa only [t,h0,h1] using hlen
  have hhalf : |(t 1-t 0)/2| ≤ d := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith
  have ha : t s-t 0=(t 1-t 0)/2 := by rw [he]; dsimp [mid]; ring
  have hb : t 1-t s=(t 1-t 0)/2 := by rw [he]; dsimp [mid]; ring
  refine ⟨γ s,⟨hp,hsK,Or.inr ⟨_,hγa,by simpa using h0,by simp⟩,?_⟩,
    ⟨hsK,hq,Or.inr ⟨_,hγb,by simp,by convert h1 using 2 <;> ring⟩,?_⟩⟩
  · rw [← h0]; change |t s-t 0|≤d; rwa [ha]
  · rw [← h1]; change |t 1-t s|≤d; rwa [hb]

theorem solution (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let g := kerrNewmanMetricField m a e
    let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m a e
    ∀ K : Set U, IsCompact K → K ⊆ D →
      closure {z : U × U | z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture g T K z.1} ⊆
        {z : U × U | z.2 ∈ causalFuture g T D z.1} := by
  dsimp only
  intro K hK hKD
  let R := shortRel m a e T K
  let JD : Set (U a × U a) := {z | z.2 ∈ causalFuture (G m a e) T (D m a e) z.1}
  have hloc (x : K) := kerrNewman_exterior_localCausalClosure m a e hp T hT x.val (hKD x.property)
  choose V hOpen hContain hDom hLocal using hloc
  have hc : K ⊆ ⋃ x : K, V x := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hContain ⟨x,hx⟩⟩
  obtain ⟨δ,hδ,hLeb⟩ := lebesgue_number_lemma_of_metric hK hOpen hc
  let d := δ/8
  have hd : 0<d := by dsimp [d]; linarith
  have hcompact (b : ℝ) : IsCompact (closure (R b)) := (hK.prod hK).of_isClosed_subset isClosed_closure
    (closure_minimal (fun z hz => ⟨hz.1,hz.2.1⟩) (hK.isClosed.prod hK.isClosed))
  have hinside (b : ℝ) : closure (R b) ⊆ K ×ˢ K := closure_minimal (fun z hz => ⟨hz.1,hz.2.1⟩) (hK.isClosed.prod hK.isClosed)
  have hbase : closure (R d) ⊆ JD := by
    intro z hz
    obtain ⟨x,hx⟩ := hLeb z.1 (hinside d hz).1
    have hdist : ∀ y∈R d, dist y.2 y.1 ≤ 2*d := by
      rintro y ⟨_,_,hJ,ht⟩
      rcases hJ with he|⟨γ,hγ,h0,h1⟩
      · rw [Set.mem_singleton_iff.mp he,dist_self]; linarith
      · have hg : IsFutureCausalCurveIn (G m a e) T (D m a e) γ :=
          ⟨hγ.1,fun s hs => ⟨hKD (hγ.2 s hs).1,(hγ.2 s hs).2⟩⟩
        have h := arc_displacement m a e hp T hT γ hg 1 (right_mem_Icc.mpr zero_le_one)
        rw [h0,h1] at h; linarith
    have hs : dist z.2 z.1 ≤ 2*d := (closure_minimal (show R d ⊆ {y | dist y.2 y.1 ≤ 2*d} from hdist)
      (isClosed_le (continuous_snd.dist continuous_fst) continuous_const)) hz
    have hpx : z.1∈V x := hx (Metric.mem_ball_self hδ)
    have hqx : z.2∈V x := hx (show dist z.2 z.1<δ by dsimp [d] at hs; linarith)
    apply hLocal x z hpx hqx
    let N : Set (U a × U a) := {y | dist y.1 z.1 < d}
    have ho : IsOpen N := (Metric.isOpen_ball.preimage continuous_fst)
    have hzn : z ∈ N := by change dist z.1 z.1<d; simpa
    apply closure_mono _ (ho.inter_closure ⟨hzn,hz⟩)
    rintro y ⟨hy,hyR⟩
    change dist y.1 z.1<d at hy
    have near (v : U a) (hv : dist v y.1 ≤ 2*d) : v∈V x := hx (by
      change dist v z.1<δ
      have := dist_triangle v y.1 z.1
      dsimp [d] at hv hy
      linarith)
    refine ⟨near y.1 (by rw [dist_self]; linarith),near y.2 (hdist y hyR),?_⟩
    rcases hyR.2.2.1 with he|⟨γ,hγ,h0,h1⟩
    · exact Or.inl he
    · refine Or.inr ⟨γ,⟨hγ.1,?_⟩,h0,h1⟩
      intro t ht
      have hg : IsFutureCausalCurveIn (G m a e) T (D m a e) γ :=
        ⟨hγ.1,fun s hs => ⟨hKD (hγ.2 s hs).1,(hγ.2 s hs).2⟩⟩
      have hh := arc_displacement m a e hp T hT γ hg t ht
      rw [h0,h1] at hh
      exact ⟨near _ (by linarith [hyR.2.2.2]),(hγ.2 t ht).2⟩
  have hdyadic (n : ℕ) : closure (R ((2:ℝ)^n*d)) ⊆ JD := by
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      let b := (2:ℝ)^n*d
      have hsup : closure (R (2*b)) ⊆ composeRel (closure (R b)) := by
        apply closure_minimal _ (compact_composition (hcompact b)).isClosed
        intro z hz
        obtain ⟨x,hx,hy⟩ := bisect m a e T K b (by dsimp [b]; positivity) hz
        exact ⟨x,subset_closure hx,subset_closure hy⟩
      intro z hz
      have he : (2:ℝ)^(n+1)*d=2*b := by dsimp [b]; ring
      rw [he] at hz
      obtain ⟨x,hx,hy⟩ := hsup hz
      exact kerrNewman_exterior_causalTransitivity m a e hp T hT z.1 (hKD (hinside b hx).1)
        x (hKD (hinside b hx).2) z.2 (hKD (hinside b hy).2) (ih hx) (ih hy)
  have hct : Continuous (fun z : U a => |z.val 0|) := by fun_prop
  obtain ⟨M,hM⟩ := hK.bddAbove_image hct.abs.continuousOn
  have bound (x : U a) (hx : x∈K) : |x.val 0|≤M := by
    simpa using hM (show |(|x.val 0|)| ∈ (fun z : U a => |(|z.val 0|)|) '' K from ⟨x,hx,rfl⟩)
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (2*M/d) (by norm_num : (1:ℝ)<2)
  apply (closure_mono ?_).trans (hdyadic n)
  rintro z ⟨h1,h2,hj⟩
  refine ⟨h1,h2,hj,?_⟩
  have ht := (div_lt_iff₀ hd).mp hn
  linarith [abs_sub (z.2.val 0) (z.1.val 0),bound z.1 h1,bound z.2 h2]
