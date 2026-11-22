-- Prove2me | solution 1 for NoHair.kerr_inner_horizon_diamond_confinement
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T23:27:10.96009+00:00
-- url     : https://prove2.me/submissions/af6b6ff6-e134-4d61-bd4f-a6aad7ba1cb8

import Definitions.Def_NoHair_KerrNewmanExteriorGeodesics
import Theorems.Thm_NoHair_kerrNewman_outerHorizon_futureTrapped
import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms

open NoHair NoHair.KNE Set Filter
open scoped Topology
open scoped BigOperators Manifold ContDiff

noncomputable section

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private abbrev T (m a e : ℝ) := kerrNewmanTimeDirection m a e
private abbrev I4 := 𝓘(ℝ,E4)
private abbrev V3 := Fin 3 → ℝ
private def dot3 (v w : V3) := ∑ i, v i*w i
private def space (v : E4) : V3 := ![v 1,v 2,v 3]
private def axis (a : ℝ) (y : E4) : V3 := ![ksNull a y 1,ksNull a y 2,ksNull a y 3]
private def timeC (v : E4) := v 0

private theorem dot_symm (u v : V3) : dot3 u v = dot3 v u := by simp [dot3, mul_comm]
private theorem dot_add_l (u v w : V3) : dot3 (u+v) w = dot3 u w + dot3 v w := by
  simp [dot3, add_mul, Finset.sum_add_distrib]
private theorem dot_add_r (u v w : V3) : dot3 u (v+w) = dot3 u v + dot3 u w := by
  simp [dot3, mul_add, Finset.sum_add_distrib]
private theorem dot_scale_l (c : ℝ) (u v : V3) : dot3 (c • u) v = c*dot3 u v := by
  simp [dot3, Finset.mul_sum, mul_assoc]
private theorem dot_scale_r (c : ℝ) (u v : V3) : dot3 u (c • v) = c*dot3 u v := by
  simp [dot3, Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc]
private theorem dot_cauchy (u v : V3) : (dot3 u v)^2 ≤ dot3 u u * dot3 v v := by
  simpa only [dot3, sq] using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) u v
private theorem axis_unit (a : ℝ) (x : U a) : dot3 (axis a x.val) (axis a x.val) = 1 := by
  simpa [dot3, axis, Fin.sum_univ_three, sq] using ks_rel a x.val x.property

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(timeC v*timeC w) + dot3 (space v) (space w) +
      ksProfile m a e x.val * (timeC v + dot3 (axis a x.val) (space v)) *
        (timeC w + dot3 (axis a x.val) (space w)) := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, Fin.sum_univ_four, ksNull_zero]
  simp [minkowski, dot3, space, timeC, axis, Fin.sum_univ_three] <;> ring

private theorem t_coords (m a e : ℝ) (x : U a) :
    timeC (T m a e x) = 1 + ksProfile m a e x.val / 2 ∧
    space (T m a e x) = -(ksProfile m a e x.val / 2) • axis a x.val := by
  refine ⟨rfl, ?_⟩
  ext i
  fin_cases i <;> rfl

private theorem metric_T (m a e : ℝ) (x : U a) (v : E4) :
    G m a e x v (T m a e x) = -timeC v + (ksProfile m a e x.val/2) *
      (timeC v + dot3 (axis a x.val) (space v)) := by
  obtain ⟨ht, hs⟩ := t_coords m a e x
  erw [metric_formula m a e x v (T m a e x), ht, hs, dot_scale_r, dot_scale_r, axis_unit, dot_symm (space v)]
  ring

private theorem time_orientation (m a e : ℝ) : IsTimeOrientation (G m a e) (T m a e) := by
  constructor
  · have hc : Continuous (fun x : U a => (T m a e x : E4)) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      have hr : Continuous (fun y : U a => ksRadius a y.val) := (continuous_ksRadius a).comp continuous_subtype_val
      have hk (i : Fin 4) : ContinuousAt (fun y : U a => ksNull a y.val i) x :=
        (ksNull_differentiableAt a x.val x.property i).continuousAt.comp continuous_subtype_val.continuousAt
      have hd := (ks_den_pos a x.val x.property).ne'
      have hf : ContinuousAt (fun y : U a => ksProfile m a e y.val) x := by
        unfold ksProfile
        fun_prop (disch := assumption)
      unfold T kerrNewmanTimeDirection
      apply (PiLp.continuous_toLp 2 _).continuousAt.comp
      apply continuousAt_pi.mpr
      intro i
      fin_cases i <;> simp only [Matrix.cons_val] <;> fun_prop
    apply continuous_iff_continuousAt.mpr
    intro x
    rw [FiberBundle.continuousAt_section]
    have htr (y : U a) : (trivializationAt E4 (TangentSpace I4) x ⟨y,T m a e y⟩).2 = (T m a e y : E4) := by
      change tangentCoordChange I4 y y y (T m a e y) = _
      exact tangentCoordChange_self (mem_extChartAt_source y)
    simpa only [htr] using hc.continuousAt (x := x)
  · intro x
    obtain ⟨ht,hs⟩ := t_coords m a e x
    erw [metric_T m a e x (T m a e x), ht, hs, dot_scale_r, axis_unit]
    nlinarith

private def radialNormal (a : ℝ) (y : E4) : V3 :=
  let r := ksRadius a y
  let k := axis a y
  let W := Wf a y
  ![r^2*k 0*W-r*k 1*W*a, r^2*k 1*W+r*k 0*W*a, (r^2+a^2)*k 2*W]

private theorem normal_geometry (a : ℝ) (x : U a) :
    dot3 (radialNormal a x.val) (axis a x.val) = 1 ∧
    dot3 (radialNormal a x.val) (radialNormal a x.val) = (ksRadius a x.val^2 + a^2)*Wf a x.val := by
  let r := ksRadius a x.val
  let k := axis a x.val
  let W := Wf a x.val
  have hrel : k 0^2+k 1^2+k 2^2=1 := ks_rel a x.val x.property
  have hW : W*(r^2+a^2*k 2^2)=1 := ks_W a x.val x.property
  let n : V3 := ![r^2*k 0*W-r*k 1*W*a, r^2*k 1*W+r*k 0*W*a, (r^2+a^2)*k 2*W]
  change dot3 n k = 1 ∧ dot3 n n = (r^2+a^2)*W
  constructor
  · calc
      dot3 n k = W*(r^2*(k 0^2+k 1^2+k 2^2)+a^2*k 2^2) := by simp [dot3, n, Fin.sum_univ_three]; ring
      _ = 1 := by rw [hrel, mul_one, hW]
  · calc
      dot3 n n = (r^2+a^2)*W*(W*(r^2*(k 0^2+k 1^2+k 2^2)+a^2*k 2^2)) := by
        simp [dot3, n, Fin.sum_univ_three]; ring
      _ = (r^2+a^2)*W := by rw [hrel, mul_one, hW, mul_one]

private theorem radial_derivative (a : ℝ) (x : U a) (v : E4) :
    fderiv ℝ (ksRadius a) x.val v = dot3 (radialNormal a x.val) (space v) := by
  have hv : ∑ i, v i • coordBasis i = v := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_four, coordBasis]
  have cp (i : Fin 4) := (hasCP_R a x.val x.property).eq i
  change ∀ (i : Fin 4), fderiv ℝ (ksRadius a) x.val (coordBasis i) = _ at cp
  calc
    _ = fderiv ℝ (ksRadius a) x.val (∑ i, v i • coordBasis i) := congrArg _ hv.symm
    _ = _ := by
      simp only [Fin.sum_univ_four, map_add, map_smul, smul_eq_mul]
      erw [cp 0, cp 1, cp 2, cp 3]
      simp [dot3, radialNormal, space, axis, dRt, Fin.sum_univ_three] <;> ring

private theorem inward (k n s : V3) (f t : ℝ) (hk : dot3 k k = 1)
    (hnk : dot3 n k = 1) (hn : dot3 n n < f) (hf : 0 < f)
    (htime : -t*t + dot3 s s + f*(t+dot3 k s)*(t+dot3 k s) ≤ 0)
    (hfuture : -t+(f/2)*(t+dot3 k s) < 0) : dot3 n s < 0 := by
  let c := f/2
  let l := t+dot3 k s
  let τ := t-c*l
  let u := s+(c*l) • k
  let b := n+(-c) • k
  have hc : 0 < c := by dsimp [c]; linarith
  have hτ : 0 < τ := by dsimp [τ,c,l]; linarith only [hfuture]
  have ff : f=2*c := by dsimp [c]; ring
  have hu : dot3 u u ≤ τ^2 := by
    have h : dot3 u u-τ^2 = -t*t+dot3 s s+f*l*l := by
      simp only [u, τ, l, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hk, dot_symm s k]
      rw [ff]
      ring
    change -t*t + dot3 s s + f*l*l ≤ 0 at htime
    linarith only [h,htime]
  have hb : dot3 b b < c^2 := by
    simp only [b, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hk, hnk, dot_symm k n]
    rw [ff] at hn
    linarith only [hn]
  have he : dot3 n s = dot3 b u - c*τ := by
    simp only [b, u, τ, l, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hnk, hk]
    ring
  have hcs := dot_cauchy b u
  have habs : |dot3 b u| < |c*τ| := sq_lt_sq.mp (by
    rw [mul_pow]
    have hb0 : 0 ≤ dot3 b b := by unfold dot3; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    exact hcs.trans_lt ((mul_le_mul_of_nonneg_left hu hb0).trans_lt (mul_lt_mul_of_pos_right hb (sq_pos_of_pos hτ))))
  rw [abs_of_pos (mul_pos hc hτ)] at habs
  rw [he]
  linarith [le_abs_self (dot3 b u)]

private theorem shell_velocity (x : U 2) (hl : 1 < ksRadius 2 x.val) (hu : ksRadius 2 x.val < 4)
    (v : E4) (hv : IsFutureCausal (G (5/2) 2 0) (T (5/2) 2 0) x v) :
    fderiv ℝ (ksRadius 2) x.val v < 0 := by
  obtain ⟨_,h1,h2⟩ := hv
  rw [metric_formula] at h1
  rw [metric_T] at h2
  obtain ⟨hnk,hn⟩ := normal_geometry 2 x
  let r := ksRadius 2 x.val
  have hr : 0 < r := x.property
  have hW : 0 < Wf 2 x.val := by unfold Wf; positivity
  have hgap : r^2+(2:ℝ)^2 < 2*(5/2)*r-0^2 := by
    change 1<r at hl
    change r<4 at hu
    nlinarith only [mul_pos (sub_pos.mpr hl) (sub_pos.mpr hu)]
  have hF : ksProfile (5/2) 2 0 x.val=(2*(5/2)*r-0^2)*Wf 2 x.val := profile_eq _ _ _ _ x.property
  have hnlt : dot3 (radialNormal 2 x.val) (radialNormal 2 x.val) < ksProfile (5/2) 2 0 x.val := by
    rw [hn,hF]
    exact mul_lt_mul_of_pos_right hgap hW
  have hFp : 0 < ksProfile (5/2) 2 0 x.val := by rw [hF]; simp only [zero_pow (by decide : 2 ≠ 0),sub_zero]; positivity
  rw [radial_derivative]
  apply inward (axis 2 x.val) (radialNormal 2 x.val) (space v) (ksProfile (5/2) 2 0 x.val) (timeC v)
    (axis_unit 2 x) hnk hnlt hFp _ h2
  simpa only [neg_mul] using h1

private abbrev Reg := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
private abbrev Met := kerrNewmanMetricField (5/2) 2 0
private abbrev Orient := kerrNewmanTimeDirection (5/2) 2 0
private abbrev UnitInterval := Icc (0:ℝ) 1

private def component (v : E4) (i : Fin 4) : ℝ := v i

private theorem clock_data (γ : ℝ → kerrNewmanSpacetime 2)
    (hγ : IsFutureCausalCurveIn Met Orient Reg γ) :
    (∀ i : Fin 4, ∀ t, HasDerivAt (fun s => (γ s).val i) (component (velocity γ t) i) t) ∧
      ∀ t∈UnitInterval, 0 < component (velocity γ t) 0 ∧ ∀ i : Fin 4, |component (velocity γ t) i| ≤ component (velocity γ t) 0 := by
  let f : ℝ → E4 := Subtype.val ∘ γ
  let I4 := 𝓘(ℝ,E4)
  have hval : ContMDiff I4 I4 1 (Subtype.val : kerrNewmanSpacetime 2 → E4) := contMDiff_subtype_val
  have hf : ContDiff ℝ 1 f := (hval.comp hγ.1).contDiff
  constructor
  · intro i t
    have hd := ((hf.differentiable_one t).hasFDerivAt).hasDerivAt
    have he := NoHair.ExteriorGeodesics.ambient_velocity 2 γ hγ.1 t (deriv f t) hd
    have hi := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t hd
    rw [he]
    exact hi
  · intro t ht
    let x := γ t
    have hr : 0 < ksRadius 2 x.val := x.property
    have hF : 0 ≤ ksProfile (5/2) 2 0 x.val := by
      unfold ksProfile
      simp only [zero_pow (by decide : 2 ≠ 0),sub_zero]
      positivity
    have hdir : 0 < component (Orient x) 0 := by change 0 < 1+ksProfile (5/2) 2 0 x.val/2; linarith
    obtain ⟨_,hn,hv,hfut⟩ := hγ.2 t ht
    have hp : IsKerrNewmanBlackHoleParams (5/2) 2 0 := by norm_num [IsKerrNewmanBlackHoleParams]
    have htime := (kerrNewman_outerHorizon_futureTrapped _ _ _ hp).1
    obtain ⟨hb,hs⟩ := NoHair.ExteriorGeodesics.cone_estimates (5/2) 2 0 x hF
      (velocity γ t) (Orient x) hn hv hfut (htime.2 x)
    have hpos : 0 < component (velocity γ t) 0 := by
      by_contra! h
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg h hdir.le)) hs
    exact ⟨hpos,fun i => (hb i).trans_eq (abs_of_pos hpos)⟩

private theorem clock_strict (γ : ℝ → kerrNewmanSpacetime 2)
    (hγ : IsFutureCausalCurveIn Met Orient Reg γ) : StrictMonoOn (fun s => (γ s).val 0) UnitInterval := by
  obtain ⟨hd,hv⟩ := clock_data γ hγ
  exact strictMonoOn_of_deriv_pos (convex_Icc 0 1) (fun t _ => (hd 0 t).continuousAt.continuousWithinAt)
    (fun t ht => (hd 0 t).deriv.symm ▸ (hv t (interior_subset ht)).1)

private theorem backwards_barrier (b : ℝ) (hb1 : 1<b) (hb4 : b<4)
    (γ : ℝ → U 2) (hγ : IsFutureCausalCurveIn Met Orient Reg γ)
    (hlast : b<ksRadius 2 (γ 1).val) (t : ℝ) (ht : t ∈ UnitInterval) : b<ksRadius 2 (γ t).val := by
  by_contra! hbad
  let z : ℝ → E4 := Subtype.val ∘ γ
  let h (s : ℝ) := ksRadius 2 (z s)
  let d (s : ℝ) := fderiv ℝ (ksRadius 2) (z s) (velocity γ s)
  have hval : ContMDiff I4 I4 1 (Subtype.val : U 2 → E4) := contMDiff_subtype_val
  have hz : ContDiff ℝ 1 z := (hval.comp hγ.1).contDiff
  have deriv (s : ℝ) : HasDerivAt h (d s) s := by
    have hcomp := mfderiv_comp s (hval.mdifferentiableAt (by simp) (x := γ s)) (hγ.1.mdifferentiableAt (by simp))
    have hinc : (mfderiv I4 I4 (Subtype.val : U 2 → E4) (γ s) : E4 →L[ℝ] E4) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ s)
    rw [hinc] at hcomp
    have hh : fderiv ℝ z s = (mfderiv 𝓘(ℝ,ℝ) I4 γ s : ℝ →L[ℝ] E4) := by
      rw [← mfderiv_eq_fderiv]
      exact hcomp
    have hv := ((hz.differentiable (by simp) s).hasFDerivAt).hasDerivAt
    rw [hh] at hv
    exact (ksRadius_differentiableAt 2 (z s) (γ s).property).hasFDerivAt.comp_hasDerivAt s hv
  have fence := image_le_of_deriv_right_lt_deriv_boundary (f := h) (f' := d)
    (B := fun _ => b) (B' := fun _ => 0) (a := t) (b := 1)
    ((continuous_ksRadius 2).comp hz.continuous).continuousOn (fun s _ => (deriv s).hasDerivWithinAt) hbad
    (fun s => hasDerivAt_const s b)
    (fun s hs he => shell_velocity (γ s) (by change 1<h s; rwa [he]) (by change h s<4; rwa [he]) (velocity γ s)
      (hγ.2 s ⟨ht.1.trans hs.1, hs.2.le⟩).2)
  exact hlast.not_ge (fence (right_mem_Icc.mpr ht.2))

private theorem coordinate_bound (γ : ℝ → U 2) (hγ : IsFutureCausalCurveIn Met Orient Reg γ)
    (t : ℝ) (ht : t ∈ UnitInterval) (i : Fin 4) :
    |(γ t).val i-(γ 0).val i| ≤ (γ 1).val 0-(γ 0).val 0 := by
  let f (t : ℝ) := (γ t).val
  let v (t : ℝ) : E4 := velocity γ t
  obtain ⟨hd,hv⟩ := clock_data γ hγ
  have mono (j d : ℝ → ℝ) (hj : ∀ s, HasDerivAt j (d s) s) (h : ∀ s∈UnitInterval, 0 ≤ d s) :
      MonotoneOn j UnitInterval := by
    have hdiff : Differentiable ℝ j := fun s => (hj s).differentiableAt
    exact monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hdiff.continuous.continuousOn hdiff.differentiableOn
      (fun s hs => (hj s).deriv.symm ▸ h s (interior_subset hs))
  have hplus : MonotoneOn (fun s => f s 0 + f s i) UnitInterval :=
    mono _ _ (fun s => (hd 0 s).add (hd i s)) fun s hs => by
      have hh := (abs_le.mp ((hv s hs).2 i)).1
      change 0 ≤ v s 0+v s i
      change -(v s 0) ≤ v s i at hh
      linarith
  have hminus : MonotoneOn (fun s => f s 0-f s i) UnitInterval :=
    mono _ _ (fun s => (hd 0 s).sub (hd i s)) fun s hs => sub_nonneg.mpr (abs_le.mp ((hv s hs).2 i)).2
  have h0 : (0:ℝ) ∈ UnitInterval := left_mem_Icc.mpr zero_le_one
  have h1 : (1:ℝ) ∈ UnitInterval := right_mem_Icc.mpr zero_le_one
  have ha := hplus h0 ht ht.1
  have hb := hminus h0 ht ht.1
  have hc := (clock_strict γ hγ).monotoneOn ht h1 ht.2
  change f t 0 ≤ f 1 0 at hc
  change |f t i-f 0 i| ≤ f 1 0-f 0 0
  beta_reduce at ha hb
  exact abs_le.mpr ⟨by linarith only [ha,hc],by linarith only [hb,hc]⟩

private theorem leg (p q : U 2) (b : ℝ) (hb : 1<b) (hb' : b<4) (hq : b<ksRadius 2 q.val)
    (hJ : q∈causalFuture Met Orient Reg p) :
    b<ksRadius 2 p.val ∧ p.val 0 ≤ q.val 0 ∧ (∀ i : Fin 4, |q.val i-p.val i| ≤ q.val 0-p.val 0) ∧
    ∀ K : Set (U 2), (∀ z : U 2, b < ksRadius 2 z.val → (∀ i : Fin 4, |z.val i-p.val i| ≤ q.val 0-p.val 0) → z∈K) →
      q ∈ causalFuture Met Orient K p := by
  rcases hJ with he | ⟨γ,hγ,h0,h1⟩
  · rcases mem_singleton_iff.mp he with rfl
    exact ⟨hq,le_rfl,fun i => by simp,fun K _ => Or.inl rfl⟩
  have hzero : (0:ℝ) ∈ UnitInterval := left_mem_Icc.mpr zero_le_one
  have hone : (1:ℝ) ∈ UnitInterval := right_mem_Icc.mpr zero_le_one
  have hr := backwards_barrier b hb hb' γ hγ (by rwa [h1])
  have hrp := hr 0 hzero
  have htime := (clock_strict γ hγ).monotoneOn hzero hone zero_le_one
  change (γ 0).val 0 ≤ (γ 1).val 0 at htime
  rw [h0,h1] at htime
  rw [h0] at hrp
  have hc (s) (hs : s∈UnitInterval) (i : Fin 4) := coordinate_bound γ hγ s hs i
  simp only [h0,h1] at hc
  refine ⟨hrp,htime,fun i => by simpa only [h1] using hc 1 hone i,?_⟩
  intro K put
  exact Or.inr ⟨γ,⟨hγ.1,fun s hs => ⟨put _ (hr s hs) (hc s hs),(hγ.2 s hs).2⟩⟩,h0,h1⟩

theorem solution :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := kerrNewmanMetricField (5/2) 2 0
    let T := kerrNewmanTimeDirection (5/2) 2 0
    ∀ p ∈ A, ∀ q ∈ A, ∃ K : Set (kerrNewmanSpacetime 2), IsCompact K ∧ K ⊆ A ∧ p ∈ K ∧ q ∈ K ∧
      ∀ x ∈ causalFuture g T A p ∩ causalPast g T A q,
        x ∈ K ∧ x ∈ causalFuture g T K p ∧ q ∈ causalFuture g T K x  := by
  dsimp only
  intro p hp q hq
  let r := fun x : U 2 => ksRadius 2 x.val
  let b := min 2 ((min (r p) (r q)+1)/2)
  have hmin : 1 < min (r p) (r q) := lt_min hp hq
  have hb : 1<b := lt_min (by norm_num) (by linarith)
  have hb' : b<4 := (min_le_left _ _).trans_lt (by norm_num)
  have hbelow : b < min (r p) (r q) := (min_le_right _ _).trans_lt (by linarith)
  have hbp := hbelow.trans_le (min_le_left _ _)
  have hbq := hbelow.trans_le (min_le_right _ _)
  let B := |q.val 0-p.val 0|
  let C (i : Fin 4) := |q.val i-p.val i|+2*B+1
  let box : Set (Fin 4 → ℝ) := Icc (fun i => p.val i-C i) (fun i => p.val i+C i)
  let H : Set E4 := (WithLp.toLp 2 '' box) ∩ {z | b ≤ ksRadius 2 z}
  let K := (Subtype.val : U 2 → E4) ⁻¹' H
  have hB : 0 ≤ B := abs_nonneg _
  have hC (i : Fin 4) : 2*B ≤ C i := by dsimp [C]; linarith [abs_nonneg (q.val i-p.val i)]
  have hH : IsCompact H := ((show IsCompact box from isCompact_Icc).image (PiLp.continuous_toLp 2 _)).inter_right
    (isClosed_le continuous_const (continuous_ksRadius 2))
  have hcompact : IsCompact K := by
    apply Subtype.isCompact_iff.mpr
    have himg : (Subtype.val : U 2 → E4) '' K = H := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩; exact hx
      · intro hz
        exact ⟨⟨z,(zero_lt_one.trans hb).trans_le hz.2⟩,hz,rfl⟩
    rwa [himg]
  have put (x : U 2) (hw : b ≤ r x) (h : ∀ i : Fin 4, |x.val i-p.val i| ≤ C i) : x∈K := by
    refine ⟨⟨WithLp.ofLp x.val,⟨?_,?_⟩,rfl⟩,hw⟩
    · intro i; have ha := (abs_le.mp (h i)).1; change p.val i-C i ≤ x.val i; linarith
    · intro i; have ha := (abs_le.mp (h i)).2; change x.val i ≤ p.val i+C i; linarith
  have hpK := put p hbp.le (fun i => by simp only [sub_self,abs_zero]; linarith [hC i])
  have hqK := put q hbq.le (fun i => by dsimp [C]; linarith)
  refine ⟨K,hcompact,fun x hx => hb.trans_le hx.2,hpK,hqK,?_⟩
  intro x hx
  obtain ⟨hbx,hxq,_,hqleg⟩ := leg x q b hb hb' hbq hx.2
  obtain ⟨_,hpx,hxi,hpleg⟩ := leg p x b hb hb' hbx hx.1
  have hdiff : q.val 0-p.val 0 ≤ B := le_abs_self _
  refine ⟨put x hbx.le (fun i => by linarith only [hxi i,hxq,hdiff,hC i,hB]),hpleg K ?_,hqleg K ?_⟩
  · intro z hz hi
    exact put z hz.le fun i => by linarith only [hi i,hxq,hdiff,hC i,hB]
  · intro z hz hi
    apply put z hz.le
    intro i
    have ht : |z.val i-p.val i| ≤ |z.val i-x.val i|+|x.val i-p.val i| := by
      simpa only [Real.dist_eq] using dist_triangle (z.val i) (x.val i) (p.val i)
    linarith only [ht,hi i,hxi i,hdiff,hC i,hB]
