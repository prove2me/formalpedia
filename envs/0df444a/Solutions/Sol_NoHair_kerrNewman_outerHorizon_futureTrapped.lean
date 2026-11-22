-- Prove2me | solution 1 for NoHair.kerrNewman_outerHorizon_futureTrapped
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:38:03.03201+00:00
-- url     : https://prove2.me/submissions/873407a9-3b5c-4116-9c92-e8ae91a74baa

import Definitions.Def_NoHair_kerrNewmanTimeDirection
import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms

open NoHair NoHair.KNE Set
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

private theorem horizon_profile (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : ksRadius a x.val = kerrNewmanOuterRadius m a e) :
    ksProfile m a e x.val = (ksRadius a x.val ^ 2 + a^2) * Wf a x.val ∧ 0 < ksProfile m a e x.val := by
  obtain ⟨hm,he⟩ := hp
  have hs := Real.sq_sqrt (show 0 ≤ m^2-a^2-e^2 by linarith)
  have hc : 2*m*ksRadius a x.val-e^2 = ksRadius a x.val^2+a^2 := by
    rw [hx]
    unfold kerrNewmanOuterRadius
    nlinarith only [hs]
  have heq : ksProfile m a e x.val = (ksRadius a x.val^2+a^2)*Wf a x.val := by
    rw [profile_eq m a e x.val x.property]
    unfold fA
    rw [hc]
  have hr : 0 < ksRadius a x.val := x.property
  refine ⟨heq, ?_⟩
  rw [heq]
  unfold Wf
  positivity

private theorem inward (k n s : V3) (f t : ℝ) (hk : dot3 k k = 1)
    (hnk : dot3 n k = 1) (hn : dot3 n n = f) (hf : 0 < f)
    (htime : -t*t + dot3 s s + f*(t+dot3 k s)*(t+dot3 k s) < 0)
    (hfuture : -t+(f/2)*(t+dot3 k s) < 0) : dot3 n s < 0 := by
  let c := f/2
  let l := t+dot3 k s
  let τ := t-c*l
  let u := s+(c*l) • k
  let b := n+(-c) • k
  have hc : 0 < c := by dsimp [c]; linarith
  have hτ : 0 < τ := by dsimp [τ,c,l]; linarith only [hfuture]
  have ff : f=2*c := by dsimp [c]; ring
  have hu : dot3 u u < τ^2 := by
    have h : dot3 u u-τ^2 = -t*t+dot3 s s+f*l*l := by
      simp only [u, τ, l, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hk, dot_symm s k]
      rw [ff]
      ring
    change -t*t + dot3 s s + f*l*l < 0 at htime
    linarith only [h,htime]
  have hb : dot3 b b = c^2 := by
    simp only [b, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hk, hnk, dot_symm k n, hn]
    rw [ff]
    ring
  have he : dot3 n s = dot3 b u - c*τ := by
    simp only [b, u, τ, l, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hnk, hk]
    ring
  have hcs := dot_cauchy b u
  rw [hb] at hcs
  have habs : |dot3 b u| < |c*τ| := sq_lt_sq.mp (by
    rw [mul_pow]
    exact hcs.trans_lt (mul_lt_mul_of_pos_left hu (sq_pos_of_pos hc)))
  rw [abs_of_pos (mul_pos hc hτ)] at habs
  rw [he]
  linarith [le_abs_self (dot3 b u)]

private theorem horizon_velocity (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : ksRadius a x.val = kerrNewmanOuterRadius m a e) (v : E4)
    (hv : IsFutureTimelike (G m a e) (T m a e) x v) : fderiv ℝ (ksRadius a) x.val v < 0 := by
  obtain ⟨h1,h2⟩ := hv
  rw [metric_formula] at h1
  rw [metric_T] at h2
  obtain ⟨hnk,hn⟩ := normal_geometry a x
  obtain ⟨hf,hp'⟩ := horizon_profile m a e hp x hx
  rw [radial_derivative]
  apply inward (axis a x.val) (radialNormal a x.val) (space v) (ksProfile m a e x.val) (timeC v)
    (axis_unit a x) hnk (hn.trans hf.symm) hp' _ h2
  simpa only [neg_mul] using h1

theorem solution (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    let T := kerrNewmanTimeDirection m a e
    let g := kerrNewmanMetricField m a e
    let b := kerrNewmanOuterRadius m a e
    IsTimeOrientation g T ∧ ∀ γ : ℝ → kerrNewmanSpacetime a,
      IsFutureTimelikeCurveIn g T univ γ → ksRadius a (γ 0).val ≤ b → ksRadius a (γ 1).val ≤ b := by
  refine ⟨time_orientation m a e, ?_⟩
  intro γ hγ h0
  let z : ℝ → E4 := Subtype.val ∘ γ
  let h (s : ℝ) := ksRadius a (z s)
  let d (s : ℝ) := fderiv ℝ (ksRadius a) (z s) (velocity γ s)
  let b := kerrNewmanOuterRadius m a e
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hz : ContDiff ℝ 1 z := (hval.comp hγ.1).contDiff
  have deriv (s : ℝ) : HasDerivAt h (d s) s := by
    have hcomp := mfderiv_comp s (hval.mdifferentiableAt (by simp) (x := γ s)) (hγ.1.mdifferentiableAt (by simp))
    have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ s) : E4 →L[ℝ] E4) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ s)
    rw [hinc] at hcomp
    have hh : fderiv ℝ z s = (mfderiv 𝓘(ℝ,ℝ) I4 γ s : ℝ →L[ℝ] E4) := by
      rw [← mfderiv_eq_fderiv]
      exact hcomp
    have hv := ((hz.differentiable (by simp) s).hasFDerivAt).hasDerivAt
    rw [hh] at hv
    exact (ksRadius_differentiableAt a (z s) (γ s).property).hasFDerivAt.comp_hasDerivAt s hv
  have fence := image_le_of_deriv_right_lt_deriv_boundary (f := h) (f' := d)
    (B := fun _ => b) (B' := fun _ => 0) (a := (0:ℝ)) (b := 1)
    ((continuous_ksRadius a).comp hz.continuous).continuousOn (fun s _ => (deriv s).hasDerivWithinAt) h0
    (fun s => hasDerivAt_const s b)
    (fun s hs he => horizon_velocity m a e hp (γ s) he (velocity γ s) (hγ.2 s (Ico_subset_Icc_self hs)).2)
  exact fence (right_mem_Icc.mpr zero_le_one)
