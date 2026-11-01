-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.reduced_integrand_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T18:58:18.143848+00:00
-- url     : https://prove2.me/submissions/85b6bc0b-0125-4700-8c12-a519c8fb5d82

import Mathlib
import Definitions.Def_OAIQ091C012
import Theorems.Thm_OAI_PositiveEinsteinFour_Boundary_zeroOrder_bound
import Theorems.Thm_OAI_PositiveEinsteinFour_hilbert_quadratic_bound_closed

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Boundary
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact triangle certificates and the full zeroth-order coupling bound. -/

namespace PositiveEinsteinFour.Boundary

open Potential

noncomputable section

/-- The cubic eigenvalue parametrization controls the potential defect using
only the minimum-eigenvalue defect and the closed spectral domain. -/
theorem spectral_potential_defect_bound {v r σ δ : ℝ}
    (hv : 0 ≤ v) (hr : 1 ≤ r) (hr2 : r ≤ 2)
    (hδ : 0 ≤ δ) (hdefect : v * (r - 1) ≤ δ)
    (hσ : σ = (3 * r - r ^ 3) / 2) :
    v ^ 2 * (1 - σ) ≤ 2 * δ ^ 2 := by
  have hd : 0 ≤ v * (r - 1) := mul_nonneg hv (by linarith)
  have hsq : (v * (r - 1)) ^ 2 ≤ δ ^ 2 := by nlinarith
  have hfac : 1 - σ = (r - 1) ^ 2 * (r + 2) / 2 := by rw [hσ]; ring
  have hmul := mul_le_mul_of_nonneg_right (show (r + 2) / 2 ≤ 2 by linarith)
    (sq_nonneg (v * (r - 1)))
  rw [hfac]
  nlinarith

end

end PositiveEinsteinFour.Boundary

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Defect
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar certificates controlling the energy defects in equation (19). -/

namespace PositiveEinsteinFour.Defect

noncomputable section

private theorem C0_0 {v : ℝ} (hlo : 0 ≤ v) (hhi : v ≤ 1) :
    1 / 2 ≤ C0 v := by
  have hz : 0 ≤ v - 0 := by linarith
  have hw : 0 ≤ 1 - v := by linarith
  have hcert : 3200 * (C0 v - 1 / 2) =
      6016 * (1 - v) ^ 2 +
      7487 * (v - 0) * (1 - v) +
      2371 * (v - 0) ^ 2 := by
    unfold C0 A0 L0
    ring
  have hp : 0 ≤ 3200 * (C0 v - 1 / 2) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem C0_1 {v : ℝ} (hlo : 1 ≤ v) (hhi : v ≤ 2) :
    1 / 2 ≤ C0 v := by
  have hz : 0 ≤ v - 1 := by linarith
  have hw : 0 ≤ 2 - v := by linarith
  have hcert : 3200 * (C0 v - 1 / 2) =
      2371 * (2 - v) ^ 2 +
      1997 * (v - 1) * (2 - v) +
      526 * (v - 1) ^ 2 := by
    unfold C0 A0 L0
    ring
  have hp : 0 ≤ 3200 * (C0 v - 1 / 2) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem disc_0 {v : ℝ} (hlo : 0 ≤ v) (hhi : v ≤ 1) :
    1 / 2 ≤ discriminantNumerator v := by
  have hz : 0 ≤ v - 0 := by linarith
  have hw : 0 ≤ 1 - v := by linarith
  have hcert : 160000 * (discriminantNumerator v - 1 / 2) =
      5098880 * (1 - v) ^ 5 +
      18922336 * (v - 0) * (1 - v) ^ 4 +
      26833814 * (v - 0) ^ 2 * (1 - v) ^ 3 +
      18127631 * (v - 0) ^ 3 * (1 - v) ^ 2 +
      5827264 * (v - 0) ^ 4 * (1 - v) +
      728216 * (v - 0) ^ 5 := by
    unfold discriminantNumerator C0 A0 L0
    ring
  have hp : 0 ≤ 160000 * (discriminantNumerator v - 1 / 2) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem disc_1 {v : ℝ} (hlo : 1 ≤ v) (hhi : v ≤ 2) :
    1 / 2 ≤ discriminantNumerator v := by
  have hz : 0 ≤ v - 1 := by linarith
  have hw : 0 ≤ 2 - v := by linarith
  have hcert : 160000 * (discriminantNumerator v - 1 / 2) =
      728216 * (2 - v) ^ 5 +
      1454896 * (v - 1) * (2 - v) ^ 4 +
      638159 * (v - 1) ^ 2 * (2 - v) ^ 3 +
      334916 * (v - 1) ^ 3 * (2 - v) ^ 2 +
      903484 * (v - 1) ^ 4 * (2 - v) +
      498272 * (v - 1) ^ 5 := by
    unfold discriminantNumerator C0 A0 L0
    ring
  have hp : 0 ≤ 160000 * (discriminantNumerator v - 1 / 2) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

theorem C0_pos {v : ℝ} (hv : 0 ≤ v) (hv2 : v ≤ 2) : 0 < C0 v := by
  by_cases hv1 : v ≤ 1
  · linarith [C0_0 hv hv1]
  · linarith [C0_1 (le_of_lt (lt_of_not_ge hv1)) hv2]

theorem disc_pos {v : ℝ} (hv : 0 ≤ v) (hv2 : v ≤ 2) : 0 < discriminantNumerator v := by
  by_cases hv1 : v ≤ 1
  · linarith [disc_0 hv hv1]
  · linarith [disc_1 (le_of_lt (lt_of_not_ge hv1)) hv2]

private theorem negative_quadratic {C B D : ℝ} (hC : 0 < C)
    (hdisc : B ^ 2 < 4 * C * D) (u : ℝ) : -C + B * u - D * u ^ 2 < 0 := by
  have hD : 0 < D := by nlinarith [sq_nonneg B]
  have hid : 4 * D * (C - B * u + D * u ^ 2) =
      (2 * D * u - B) ^ 2 + (4 * C * D - B ^ 2) := by ring
  have hpos : 0 < 4 * D * (C - B * u + D * u ^ 2) := by
    rw [hid]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sub_pos.mpr hdisc)
  have hpoly : 0 < C - B * u + D * u ^ 2 :=
    (mul_pos_iff_of_pos_left (by positivity : 0 < 4 * D)).mp hpos
  linarith

/-- The exact upper bound for the derivative with respect to an energy defect
is negative on the open spectral interval, for every real energy ratio. -/
theorem energy_defect_derivative_neg {v : ℝ} (hv : 0 < v) (hv2 : v < 2) (u : ℝ) :
    A0 v * (1 + u) ^ 2 + L0 v * (1 + u) -
      (17 / 10) * (7 / 5 + (1 + 2 * v / (5 * (2 - v))) * u ^ 2) < 0 := by
  let D : ℝ := (17 / 10) - A0 v + 2 * (17 / 10) * v / (5 * (2 - v))
  have hden : 0 < 2 - v := by linarith
  have hid : discriminantNumerator v =
      (2 - v) * (4 * C0 v * D - (2 * A0 v + L0 v) ^ 2) := by
    unfold discriminantNumerator D
    field_simp [ne_of_gt hden]
  have hdisc : (2 * A0 v + L0 v) ^ 2 < 4 * C0 v * D := by
    have hp := disc_pos hv.le hv2.le
    rw [hid] at hp
    have := (mul_pos_iff_of_pos_left hden).mp hp
    linarith
  have hquad := negative_quadratic (C0_pos hv.le hv2.le) hdisc u
  have heq : A0 v * (1 + u) ^ 2 + L0 v * (1 + u) -
      (17 / 10) * (7 / 5 + (1 + 2 * v / (5 * (2 - v))) * u ^ 2) =
      -C0 v + (2 * A0 v + L0 v) * u - D * u ^ 2 := by
    unfold C0 D
    ring
  rwa [heq]

end

end PositiveEinsteinFour.Defect

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Energy
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removal of the energy defects

The right side of equation (19) is kept as an actual function of its two
energies. Its derivative estimate uses the scalar discriminant; continuity supplies
the zero-energy endpoints.
-/

namespace PositiveEinsteinFour.Energy

open Defect

noncomputable section

/-- The homogeneous form of the strict scalar discriminant estimate. -/
theorem homogeneous_derivative_nonpos
    {v : ℝ} (hv : 0 < v) (hv2 : v < 2) (r s : ℝ) :
    A0 v * (r + s) ^ 2 + L0 v * r * (r + s) -
      (17 / 10) * ((7 / 5) * r ^ 2 + (1 + 2 * v / (5 * (2 - v))) * s ^ 2) ≤ 0 := by
  by_cases hr : r = 0
  · subst r
    have hv_sq : v ^ 2 ≤ 4 := by nlinarith
    have hA : A0 v ≤ 477 / 320 := by
      unfold A0
      nlinarith
    have hsub : 0 < 2 - v := by linarith
    have hden : 0 < 5 * (2 - v) := by positivity
    have hfrac : 0 ≤ 2 * v / (5 * (2 - v)) := by positivity
    have hcoef : A0 v - (17 / 10) * (1 + 2 * v / (5 * (2 - v))) ≤ 0 := by
      linarith
    have h := mul_nonpos_of_nonpos_of_nonneg hcoef (sq_nonneg s)
    nlinarith
  · have h := energy_defect_derivative_neg hv hv2 (s / r)
    have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) (le_of_lt h)
    have hid : r ^ 2 * (A0 v * (1 + s / r) ^ 2 + L0 v * (1 + s / r) -
        (17 / 10) * (7 / 5 + (1 + 2 * v / (5 * (2 - v))) * (s / r) ^ 2)) =
        A0 v * (r + s) ^ 2 + L0 v * r * (r + s) -
          (17 / 10) * ((7 / 5) * r ^ 2 +
            (1 + 2 * v / (5 * (2 - v))) * s ^ 2) := by
      field_simp [hr, ne_of_gt (sub_pos.mpr hv2)]
    rwa [hid] at hm

private theorem hasDerivAt_mul_sqrt {e : ℝ} (he : 0 < e) :
    HasDerivAt (fun x : ℝ => x * Real.sqrt x) ((3 / 2) * Real.sqrt e) e := by
  have h := (hasDerivAt_id e).mul (Real.hasDerivAt_sqrt (ne_of_gt he))
  refine h.congr_deriv ?_
  · have hs : Real.sqrt e ≠ 0 := ne_of_gt (Real.sqrt_pos.2 he)
    simp only [id_eq]
    field_simp [hs]
    nlinarith [Real.sq_sqrt he.le]

/-- The derivative with respect to the first energy, for positive first energy. -/
theorem quarticEnergy_hasDerivAt_left
    (v b e0 f0 g gb H Hb f : ℝ) {e : ℝ} (he : 0 < e) :
    HasDerivAt (fun x => quarticEnergy v b e0 f0 g gb H Hb x f)
      ((3 / 4) * Real.sqrt (3 / 5) * gradientSum e0 f0 * scalarWeight v b * Real.sqrt e +
        (9 / 64) * (gradientSum e0 f0) ^ 2 * H -
        (17 / 10) * ((e - (3 / 5) * e0) / v + (f - (3 / 5) * f0) / b + (e + f) / v)) e := by
  have hfirst := ((hasDerivAt_mul_sqrt he).const_mul (scalarWeight v b)).add_const
    (scalarWeight b v * (f * Real.sqrt f))
  have hsecond := (((hasDerivAt_id e).sub_const e0).const_mul H).add_const
    (g * e0 + gb * f0 + Hb * (f - f0))
  have hthird := ((hasDerivAt_id e).add_const f).mul
    ((((hasDerivAt_id e).sub_const ((3 / 5) * e0)).div_const v).add_const
      ((f - (3 / 5) * f0) / b))
  refine ((((hfirst.const_mul ((1 / 2) * Real.sqrt (3 / 5) * gradientSum e0 f0)).add
    (hsecond.const_mul ((9 / 64) * (gradientSum e0 f0) ^ 2))).sub
    (hthird.const_mul (17 / 10))).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · beta_reduce
    unfold quarticEnergy
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [id_eq]
    ring

/-- The actual first-energy derivative in (19) is nonpositive. The elementary
bounds on `H` are exactly the displayed bounds for the defect coefficient. -/
theorem quarticEnergy_left_derivative_nonpos
    {v b e0 f0 H e f : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hsum : v + b ≤ 2)
    (he0 : 0 ≤ e0) (hf0 : 0 ≤ f0) (he : e0 ≤ e) (hf : f0 ≤ f)
    (hH0 : 0 ≤ H) (hH : H ≤ 15 / 2 + 2 * v / 3) :
    (3 / 4) * Real.sqrt (3 / 5) * gradientSum e0 f0 * scalarWeight v b * Real.sqrt e +
      (9 / 64) * (gradientSum e0 f0) ^ 2 * H -
      (17 / 10) * ((e - (3 / 5) * e0) / v + (f - (3 / 5) * f0) / b + (e + f) / v) ≤ 0 := by
  have hv2 : v < 2 := by linarith
  have he_nonneg : 0 ≤ e := le_trans he0 he
  have hf_nonneg : 0 ≤ f := le_trans hf0 hf
  let r := Real.sqrt e
  let s := Real.sqrt f
  let k := Real.sqrt (3 / 5 : ℝ)
  let z := gradientSum e0 f0
  have hr : 0 ≤ r := Real.sqrt_nonneg e
  have hs : 0 ≤ s := Real.sqrt_nonneg f
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hk_sq : k ^ 2 = (3 / 5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hz : 0 ≤ z := by dsimp [z, gradientSum]; positivity
  have hz_bound : z ≤ k * (r + s) := by
    exact mul_le_mul_of_nonneg_left
      (add_le_add (Real.sqrt_le_sqrt he) (Real.sqrt_le_sqrt hf)) hk
  have hM0 : 0 ≤ scalarWeight v b := by unfold scalarWeight; linarith
  have hM : scalarWeight v b ≤ 7 / 4 - 3 * v / 4 := by
    unfold scalarWeight
    linarith
  have hU : 0 ≤ 7 / 4 - 3 * v / 4 := by linarith
  have hHmax : 0 ≤ 15 / 2 + 2 * v / 3 := by positivity
  have hfirst : (3 / 4) * k * z * scalarWeight v b * r * v ≤
      L0 v * r * (r + s) := by
    calc
      _ ≤ (3 / 4) * k * (k * (r + s)) * (7 / 4 - 3 * v / 4) * r * v := by
        gcongr
      _ = ((3 / 4) * k ^ 2 * (7 / 4 - 3 * v / 4) * v) * r * (r + s) := by ring
      _ = _ := by rw [hk_sq]; unfold L0; ring
  have hsecond : (9 / 64) * z ^ 2 * H * v ≤ A0 v * (r + s) ^ 2 := by
    calc
      _ ≤ (9 / 64) * (k * (r + s)) ^ 2 * (15 / 2 + 2 * v / 3) * v := by
        gcongr
      _ = (9 / 64) * k ^ 2 * (r + s) ^ 2 * (15 / 2 + 2 * v / 3) * v := by ring
      _ = _ := by rw [hk_sq]; unfold A0; ring
  have hratio : v / (2 - v) ≤ v / b := by
    apply div_le_div_of_nonneg_left hv.le hb
    linarith
  have hradial : (7 / 5) * e + (1 + 2 * v / (5 * (2 - v))) * f ≤
      v * ((e - (3 / 5) * e0) / v + (f - (3 / 5) * f0) / b + (e + f) / v) := by
    calc
      _ = (7 / 5) * e + f + (v / (2 - v)) * ((2 / 5) * f) := by
        field_simp [ne_of_gt (sub_pos.mpr hv2)]
        ring
      _ ≤ (7 / 5) * e + f + (v / b) * ((2 / 5) * f) := by gcongr
      _ ≤ 2 * e + f - (3 / 5) * e0 + (v / b) * (f - (3 / 5) * f0) := by
        gcongr <;> linarith
      _ = _ := by field_simp [ne_of_gt hv, ne_of_gt hb]; ring
  have hhom := homogeneous_derivative_nonpos hv hv2 r s
  have hre : r ^ 2 = e := Real.sq_sqrt he_nonneg
  have hsf : s ^ 2 = f := Real.sq_sqrt hf_nonneg
  have hscaled : v *
      ((3 / 4) * k * z * scalarWeight v b * r + (9 / 64) * z ^ 2 * H -
        (17 / 10) * ((e - (3 / 5) * e0) / v + (f - (3 / 5) * f0) / b + (e + f) / v)) ≤ 0 := by
    have hcomparison : v *
        ((3 / 4) * k * z * scalarWeight v b * r + (9 / 64) * z ^ 2 * H -
          (17 / 10) * ((e - (3 / 5) * e0) / v + (f - (3 / 5) * f0) / b + (e + f) / v)) ≤
        A0 v * (r + s) ^ 2 + L0 v * r * (r + s) -
          (17 / 10) * ((7 / 5) * r ^ 2 + (1 + 2 * v / (5 * (2 - v))) * s ^ 2) := by
      rw [hre, hsf]
      nlinarith only [hfirst, hsecond, hradial]
    exact le_trans hcomparison hhom
  exact nonpos_of_mul_nonpos_right hscaled hv

/-- Monotonicity in the first defect, including a zero radial-energy endpoint. -/
theorem quarticEnergy_left_antitone
    {v b e0 f0 H e f : ℝ} (g gb Hb : ℝ)
    (hv : 0 < v) (hb : 0 < b) (hsum : v + b ≤ 2)
    (he0 : 0 ≤ e0) (hf0 : 0 ≤ f0) (he : e0 ≤ e) (hf : f0 ≤ f)
    (hH0 : 0 ≤ H) (hH : H ≤ 15 / 2 + 2 * v / 3) :
    quarticEnergy v b e0 f0 g gb H Hb e f ≤
      quarticEnergy v b e0 f0 g gb H Hb e0 f := by
  have hc : Continuous (fun x => quarticEnergy v b e0 f0 g gb H Hb x f) := by
    unfold quarticEnergy
    fun_prop
  have hantitone : AntitoneOn (fun x => quarticEnergy v b e0 f0 g gb H Hb x f)
      (Set.Ici e0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici e0) hc.continuousOn
    · intro x hx
      rw [interior_Ici] at hx
      exact (quarticEnergy_hasDerivAt_left v b e0 f0 g gb H Hb f
        (lt_of_le_of_lt he0 hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(quarticEnergy_hasDerivAt_left v b e0 f0 g gb H Hb f
        (lt_of_le_of_lt he0 hx)).deriv]
      exact quarticEnergy_left_derivative_nonpos hv hb hsum he0 hf0 hx.le hf hH0 hH
  exact hantitone (by first | simp | exact_mod_cast le_top) he he

/-- Exchanging the two Weyl blocks preserves the energy expression. -/
theorem quarticEnergy_swap (v b e0 f0 g gb H Hb e f : ℝ) :
    quarticEnergy v b e0 f0 g gb H Hb e f =
      quarticEnergy b v f0 e0 gb g Hb H f e := by
  unfold quarticEnergy gradientSum
  ring

/-- The full removal of both nonnegative energy defects in equation (19).
The coefficient bounds are the elementary pointwise bounds displayed before
the manuscript's scalar discriminant calculation; all zero-energy cases are
included by continuity. -/
theorem remove_energy_defects
    {v b e0 f0 H Hb e f : ℝ} (g gb : ℝ)
    (hv : 0 < v) (hb : 0 < b) (hsum : v + b ≤ 2)
    (he0 : 0 ≤ e0) (hf0 : 0 ≤ f0) (he : e0 ≤ e) (hf : f0 ≤ f)
    (hH0 : 0 ≤ H) (hH : H ≤ 15 / 2 + 2 * v / 3)
    (hHb0 : 0 ≤ Hb) (hHb : Hb ≤ 15 / 2 + 2 * b / 3) :
    quarticEnergy v b e0 f0 g gb H Hb e f ≤
      quarticEnergy v b e0 f0 g gb H Hb e0 f0 := by
  calc
    _ ≤ quarticEnergy v b e0 f0 g gb H Hb e0 f :=
      quarticEnergy_left_antitone g gb Hb hv hb hsum he0 hf0 he hf hH0 hH
    _ = quarticEnergy b v f0 e0 gb g Hb H f e0 := quarticEnergy_swap _ _ _ _ _ _ _ _ _ _
    _ ≤ quarticEnergy b v f0 e0 gb g Hb H f0 e0 :=
      quarticEnergy_left_antitone gb g H hb hv (by linarith) hf0 he0 hf le_rfl hHb0 hHb
    _ = _ := (quarticEnergy_swap _ _ _ _ _ _ _ _ _ _).symm

/-- The elementary sectional-domain bounds for the coefficient `H_d`. -/
theorem defectCoefficient_bounds {v y : ℝ}
    (hv : 0 ≤ v) (hy : 0 ≤ y) (hsum : v + y ≤ 2) :
    0 ≤ defectCoefficient v y ∧ defectCoefficient v y ≤ 15 / 2 + 2 * v / 3 := by
  unfold defectCoefficient
  constructor <;> linarith

/-- Removal of defects with the actual curvature coefficient `H_d` on the
sectional-positivity domain. -/
theorem remove_energy_defects_from_spectral_bounds
    {v b x y e0 f0 e f : ℝ} (g gb : ℝ)
    (hv : 0 < v) (hb : 0 < b) (hvx : v ≤ x) (hby : b ≤ y) (hxy : x + y ≤ 2)
    (he0 : 0 ≤ e0) (hf0 : 0 ≤ f0) (he : e0 ≤ e) (hf : f0 ≤ f) :
    quarticEnergy v b e0 f0 g gb (defectCoefficient v y) (defectCoefficient b x) e f ≤
      quarticEnergy v b e0 f0 g gb (defectCoefficient v y) (defectCoefficient b x) e0 f0 := by
  have hH := defectCoefficient_bounds (v := v) (y := y) hv.le (by linarith) (by linarith)
  have hHb := defectCoefficient_bounds (v := b) (y := x) hb.le (by linarith) (by linarith)
  exact remove_energy_defects g gb hv hb (by linarith) he0 hf0 he hf hH.1 hH.2 hHb.1 hHb.2

end
end PositiveEinsteinFour.Energy

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Quartic
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar certificates for the quartic comparison

Exact rational signs for equation (20) and Lemma 7.2 of the manuscript.
The Bernstein expansions give exact rational coefficients and their signs.
-/

namespace PositiveEinsteinFour.Quartic

noncomputable section

theorem G_lower {u : ℝ} (hlo : 0 ≤ u) (hhi : u ≤ 1) :
    9 / 10 ≤ G u := by
  have hz : 0 ≤ ((u - 0) / 1) := by linarith
  have hw : 0 ≤ 1 - ((u - 0) / 1) := by linarith
  have hcert : 3200 * (G u - 9 / 10) =
      45 * (1 - ((u - 0) / 1)) ^ 4 +
      5130 * ((u - 0) / 1) * (1 - ((u - 0) / 1)) ^ 3 +
      18009 * ((u - 0) / 1) ^ 2 * (1 - ((u - 0) / 1)) ^ 2 +
      19908 * ((u - 0) / 1) ^ 3 * (1 - ((u - 0) / 1)) +
      6948 * ((u - 0) / 1) ^ 4 := by
    unfold G
    ring
  have hp : 0 ≤ 3200 * (G u - 9 / 10) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

theorem H_lower {u : ℝ} (hlo : 0 ≤ u) (hhi : u ≤ 1) :
    1 / 4 ≤ H u := by
  have hz : 0 ≤ ((u - 0) / 1) := by linarith
  have hw : 0 ≤ 1 - ((u - 0) / 1) := by linarith
  have hcert : 12800 * (H u - 1 / 4) =
      481 * (1 - ((u - 0) / 1)) ^ 4 +
      5974 * ((u - 0) / 1) * (1 - ((u - 0) / 1)) ^ 3 +
      26592 * ((u - 0) / 1) ^ 2 * (1 - ((u - 0) / 1)) ^ 2 +
      49336 * ((u - 0) / 1) ^ 3 * (1 - ((u - 0) / 1)) +
      36112 * ((u - 0) / 1) ^ 4 := by
    unfold H
    ring
  have hp : 0 ≤ 12800 * (H u - 1 / 4) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

theorem Z_nonpos_small {u : ℝ} (hlo : 0 ≤ u) (hhi : u ≤ (1 / 16)) :
    Z u ≤ 0 := by
  have hz : 0 ≤ ((u - 0) / (1 / 16)) := by linarith
  have hw : 0 ≤ 1 - ((u - 0) / (1 / 16)) := by linarith
  have hcert : 175921860444160000 * (-Z u) =
      96447356102246400 * (1 - ((u - 0) / (1 / 16))) ^ 8 +
      705779842469068800 * ((u - 0) / (1 / 16)) * (1 - ((u - 0) / (1 / 16))) ^ 7 +
      2233691314254249984 * ((u - 0) / (1 / 16)) ^ 2 * (1 - ((u - 0) / (1 / 16))) ^ 6 +
      3981178688979861504 * ((u - 0) / (1 / 16)) ^ 3 * (1 - ((u - 0) / (1 / 16))) ^ 5 +
      4351464125411033088 * ((u - 0) / (1 / 16)) ^ 4 * (1 - ((u - 0) / (1 / 16))) ^ 4 +
      2966650978945646592 * ((u - 0) / (1 / 16)) ^ 5 * (1 - ((u - 0) / (1 / 16))) ^ 3 +
      1218436049307151872 * ((u - 0) / (1 / 16)) ^ 6 * (1 - ((u - 0) / (1 / 16))) ^ 2 +
      270150054573127104 * ((u - 0) / (1 / 16)) ^ 7 * (1 - ((u - 0) / (1 / 16))) +
      23720719937369031 * ((u - 0) / (1 / 16)) ^ 8 := by
    unfold Z L A G H
    ring
  have hp : 0 ≤ 175921860444160000 * (-Z u) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

theorem discriminant_nonneg {u : ℝ} (hlo : (1 / 16) ≤ u) (hhi : u ≤ 1) :
    0 ≤ discriminant u := by
  have hz : 0 ≤ ((u - (1 / 16)) / (15 / 16)) := by linarith
  have hw : 0 ≤ 1 - ((u - (1 / 16)) / (15 / 16)) := by linarith
  have hcert : 49517601571415210995964968960000 * (discriminant u) =
      6168574436959761676638843427263 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 16 +
      424154777452262164887934458457728 * ((u - (1 / 16)) / (15 / 16)) * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 15 +
      5745102856303709684919706005519360 * ((u - (1 / 16)) / (15 / 16)) ^ 2 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 14 +
      39024793730224628563705435309178880 * ((u - (1 / 16)) / (15 / 16)) ^ 3 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 13 +
      166503926549188231049624719485173760 * ((u - (1 / 16)) / (15 / 16)) ^ 4 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 12 +
      495120111132825129677055074274115584 * ((u - (1 / 16)) / (15 / 16)) ^ 5 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 11 +
      1095446172671702946521384982794993664 * ((u - (1 / 16)) / (15 / 16)) ^ 6 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 10 +
      1906132635982707314500534987464376320 * ((u - (1 / 16)) / (15 / 16)) ^ 7 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 9 +
      2763874657831845070490101698275573760 * ((u - (1 / 16)) / (15 / 16)) ^ 8 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 8 +
      3521116051815405437512553791928401920 * ((u - (1 / 16)) / (15 / 16)) ^ 9 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 7 +
      4016512417947710025750779579496136704 * ((u - (1 / 16)) / (15 / 16)) ^ 10 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 6 +
      3969034635025022417002617853490233344 * ((u - (1 / 16)) / (15 / 16)) ^ 11 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 5 +
      3184400848861595859007882321157160960 * ((u - (1 / 16)) / (15 / 16)) ^ 12 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 4 +
      1930552432251624252702533599761530880 * ((u - (1 / 16)) / (15 / 16)) ^ 13 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 3 +
      815949494369681637713395413323612160 * ((u - (1 / 16)) / (15 / 16)) ^ 14 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 2 +
      212811373474353171256131286632235008 * ((u - (1 / 16)) / (15 / 16)) ^ 15 * (1 - ((u - (1 / 16)) / (15 / 16))) +
      25756730625900971793653188849041408 * ((u - (1 / 16)) / (15 / 16)) ^ 16 := by
    unfold discriminant Z L A G H
    ring
  have hp : 0 ≤ 49517601571415210995964968960000 * (discriminant u) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem sqrt_comparison {a g h l u : ℝ}
    (ha : 0 ≤ a) (hg : 0 ≤ g) (hh : 0 ≤ h) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hz : l ^ 2 - 4 * a * (g + u ^ 2 * h) ≤
      8 * a * u * Real.sqrt g * Real.sqrt h) :
    l ≤ 2 * Real.sqrt a * (Real.sqrt g + u * Real.sqrt h) := by
  have ht : 0 ≤ 2 * Real.sqrt a * (Real.sqrt g + u * Real.sqrt h) := by positivity
  have heq : (2 * Real.sqrt a * (Real.sqrt g + u * Real.sqrt h)) ^ 2 =
      4 * a * (g + u ^ 2 * h) + 8 * a * u * Real.sqrt g * Real.sqrt h := by
    calc
      _ = 4 * (Real.sqrt a) ^ 2 *
          ((Real.sqrt g) ^ 2 + u ^ 2 * (Real.sqrt h) ^ 2 +
            2 * u * Real.sqrt g * Real.sqrt h) := by ring
      _ = _ := by rw [Real.sq_sqrt ha, Real.sq_sqrt hg, Real.sq_sqrt hh]; ring
  apply (sq_le_sq₀ hl ht).mp
  rw [heq]
  linarith

/-- The square-root comparison deduced from the two discriminant certificates. -/
theorem root_bound {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    L u ≤ 2 * Real.sqrt (A u) * (Real.sqrt (G u) + u * Real.sqrt (H u)) := by
  have ha : 0 ≤ A u := by unfold A; positivity
  have hg : 0 ≤ G u := le_trans (by norm_num) (G_lower hu hu1)
  have hh : 0 ≤ H u := le_trans (by norm_num) (H_lower hu hu1)
  have hl : 0 ≤ L u := by unfold L; positivity
  apply sqrt_comparison ha hg hh hl hu
  change Z u ≤ 8 * A u * u * Real.sqrt (G u) * Real.sqrt (H u)
  by_cases hsmall : u ≤ 1 / 16
  · exact (Z_nonpos_small hu hsmall).trans (by positivity)
  · have hd := discriminant_nonneg (le_of_lt (lt_of_not_ge hsmall)) hu1
    unfold discriminant at hd
    have hk : 0 ≤ 8 * A u * u * Real.sqrt (G u) * Real.sqrt (H u) := by positivity
    have hksq : (8 * A u * u * Real.sqrt (G u) * Real.sqrt (H u)) ^ 2 =
        64 * A u ^ 2 * u ^ 2 * G u * H u := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hg, Real.sq_sqrt hh]
      ring
    have hs : (Z u) ^ 2 ≤
        (8 * A u * u * Real.sqrt (G u) * Real.sqrt (H u)) ^ 2 := by
      rw [hksq]
      linarith
    exact le_trans (le_abs_self _) ((sq_le_sq₀ (abs_nonneg _) hk).mp (by simpa using hs))

private theorem quotient_amgm {a g v : ℝ} (ha : 0 ≤ a) (hg : 0 ≤ g) (hv : 0 < v) :
    2 * Real.sqrt (a * g) ≤ a / v + g * v := by
  have hx : 0 ≤ a / v := div_nonneg ha hv.le
  have hy : 0 ≤ g * v := mul_nonneg hg hv.le
  have hprod : a / v * (g * v) = a * g := by field_simp
  have heq : Real.sqrt (a / v) * Real.sqrt (g * v) = Real.sqrt (a * g) := by
    rw [← Real.sqrt_mul hx, hprod]
  have hsq := sq_nonneg (Real.sqrt (a / v) - Real.sqrt (g * v))
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  nlinarith

/-- The relaxed quartic difference after division by `v b P⁴` is nonnegative.
This is the final arithmetic-geometric-mean step in equation (20). -/
theorem relaxed_quartic_nonneg {u v b : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 < v) (hb : 0 < b) :
    0 ≤ A u / v + A u * u ^ 2 / b + G u * v + H u * b - L u := by
  have ha : 0 ≤ A u := by unfold A; positivity
  have hg : 0 ≤ G u := le_trans (by norm_num) (G_lower hu hu1)
  have hh : 0 ≤ H u := le_trans (by norm_num) (H_lower hu hu1)
  have hamgm1 := quotient_amgm ha hg hv
  have hamgm2 := quotient_amgm (mul_nonneg ha (sq_nonneg u)) hh hb
  have hs1 : Real.sqrt (A u * G u) = Real.sqrt (A u) * Real.sqrt (G u) :=
    Real.sqrt_mul ha _
  have hs2 : Real.sqrt (A u * u ^ 2 * H u) =
      u * Real.sqrt (A u) * Real.sqrt (H u) := by
    rw [show A u * u ^ 2 * H u = u ^ 2 * (A u * H u) by ring,
      Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq hu, Real.sqrt_mul ha]
    ring
  rw [hs1] at hamgm1
  rw [hs2] at hamgm2
  have hroot := root_bound hu hu1
  nlinarith

/-- Equation (20) after normalizing the larger gradient parameter to one
and enlarging the spectral defects to `(δ, 0)`, exactly as in the paper. -/
theorem enlarged_quartic_bound {u v b : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 < v) (hb : 0 < b) :
    (27 / 128) * v * b * (1 + u) ^ 2 *
        ((19 / 3 - 3 * v - 17 * b / 12) + (7 / 2 - 19 * b / 12) * u ^ 2) +
      (3 / 4) * v * b * (1 + u) *
        ((1 - 3 * (v - b) / 8) + (1 - 3 * (b - v) / 8) * u ^ 3) ≤
      (67 / 50 + 27 * v * b / 100) * (1 + u ^ 2) * (b + v * u ^ 2) := by
  have hp := mul_nonneg (mul_pos hv hb).le (relaxed_quartic_nonneg hu hu1 hv hb)
  have hid :
      (67 / 50 + 27 * v * b / 100) * (1 + u ^ 2) * (b + v * u ^ 2) -
        ((27 / 128) * v * b * (1 + u) ^ 2 *
          ((19 / 3 - 3 * v - 17 * b / 12) + (7 / 2 - 19 * b / 12) * u ^ 2) +
          (3 / 4) * v * b * (1 + u) *
            ((1 - 3 * (v - b) / 8) + (1 - 3 * (b - v) / 8) * u ^ 3)) =
      v * b * (A u / v + A u * u ^ 2 / b + G u * v + H u * b - L u) := by
    unfold A G H L
    field_simp
    ring
  rw [← hid] at hp
  linarith

private theorem spectral_polynomial_nonneg {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) :
    0 ≤ 4 * r * (r + 3) - (r - 1) * (r + 2) * (r + 1) ^ 2 := by
  have hz : 0 ≤ r - 1 := by linarith
  have hz1 : 0 ≤ 1 - (r - 1) := by linarith
  have hcert : 4 * r * (r + 3) - (r - 1) * (r + 2) * (r + 1) ^ 2 =
      16 * (1 - (r - 1)) ^ 4 + 72 * (r - 1) * (1 - (r - 1)) ^ 3 +
      108 * (r - 1) ^ 2 * (1 - (r - 1)) ^ 2 +
      57 * (r - 1) ^ 3 * (1 - (r - 1)) + 4 * (r - 1) ^ 4 := by ring
  rw [hcert]
  positivity

/-- The spectral-shape term in the quartic projection cost is bounded by
twice the minimum-eigenvalue defect. This keeps the cubic invariant of the
normalized trace-free block, instead of assuming an axial eigenvalue shape. -/
theorem spectral_defect_bound {v r σ ρ : ℝ}
    (hv : 0 ≤ v) (hr : 1 ≤ r) (hr2 : r ≤ 2) (hvr : v * r ≤ 2)
    (hσ : σ = (3 * r - r ^ 3) / 2) (hρ : ρ ^ 2 = 1 - σ ^ 2) :
    -σ * v + ρ ^ 2 * v ^ 2 / 4 ≤ -v + 2 * (v * r - v) := by
  have hp := spectral_polynomial_nonneg hr hr2
  have hrpos : 0 < r := by linarith
  have hplus : 1 + σ = (2 - r) * (r + 1) ^ 2 / 2 := by rw [hσ]; ring
  have hminus : 1 - σ = (r - 1) ^ 2 * (r + 2) / 2 := by rw [hσ]; ring
  have hplus_nonneg : 0 ≤ 1 + σ := by rw [hplus]; positivity
  have hprod1 := mul_nonneg (show 0 ≤ 2 - r by linarith) hp
  have hprod2 := mul_nonneg (show 0 ≤ 2 - r * v by nlinarith)
    (mul_nonneg (mul_nonneg (show 0 ≤ r - 1 by linarith)
      (show 0 ≤ r + 2 by linarith)) hplus_nonneg)
  have hid :
      8 * r * (2 - (r - 1) * (r + 2) / 2 * (1 + v * (1 + σ) / 4)) =
      (2 - r) * (4 * r * (r + 3) - (r - 1) * (r + 2) * (r + 1) ^ 2) +
        (2 - r * v) * (r - 1) * (r + 2) * (1 + σ) := by
    rw [hσ]
    ring
  have hbound : (r - 1) * (r + 2) / 2 * (1 + v * (1 + σ) / 4) ≤ 2 := by
    have hnonneg : 0 ≤ 8 * r *
        (2 - (r - 1) * (r + 2) / 2 * (1 + v * (1 + σ) / 4)) := by
      rw [hid]
      nlinarith
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbound
    (mul_nonneg hv (show 0 ≤ r - 1 by linarith))
  have hshape :
      v * (r - 1) * ((r - 1) * (r + 2) / 2 * (1 + v * (1 + σ) / 4)) =
        v * (1 - σ) * (1 + v * (1 + σ) / 4) := by rw [hminus]; ring
  rw [hshape] at hmul
  rw [hρ]
  nlinarith

private theorem projection_enlargement {u v b V W : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hW : 0 ≤ W) (hsum : V + W ≤ 2 - v - b) :
    projectionBound v b V W + projectionBound b v W V * u ^ 2 ≤
      (19 / 3 - 3 * v - 17 * b / 12) + (7 / 2 - 19 * b / 12) * u ^ 2 := by
  have hsquare : 0 ≤ 1 - u ^ 2 := by nlinarith
  have hterm1 := mul_nonneg hsquare hW
  have hterm2 := mul_nonneg (show 0 ≤ 2 + (7 / 12 : ℝ) * u ^ 2 by positivity)
    (show 0 ≤ 2 - v - b - V - W by linarith)
  unfold projectionBound
  nlinarith

private theorem normalized_margin_nonneg {u v b V W : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 < v) (hb : 0 < b)
    (hW : 0 ≤ W) (hsum : V + W ≤ 2 - v - b) :
    0 ≤ quarticMargin v b V W 1 u := by
  have hlarge := enlarged_quartic_bound hu hu1 hv hb
  have hproj := projection_enlargement hu hu1 hW hsum
  have hmul := mul_le_mul_of_nonneg_left hproj
    (show 0 ≤ (27 / 128 : ℝ) * v * b * (1 + u) ^ 2 by positivity)
  unfold quarticMargin
  norm_num only [one_pow, mul_one]
  linarith

theorem quarticMargin_swap (v b V W P Q : ℝ) :
    quarticMargin b v W V Q P = quarticMargin v b V W P Q := by
  unfold quarticMargin projectionBound
  ring

private theorem ordered_margin_nonneg {v b V W P Q : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hW : 0 ≤ W)
    (hsum : V + W ≤ 2 - v - b) (hP : 0 < P) (hQ : 0 ≤ Q) (hQP : Q ≤ P) :
    0 ≤ quarticMargin v b V W P Q := by
  have hu : 0 ≤ Q / P := div_nonneg hQ hP.le
  have hu1 : Q / P ≤ 1 := (div_le_one hP).2 hQP
  have hnorm := normalized_margin_nonneg hu hu1 hv hb hW hsum
  have hid : quarticMargin v b V W P Q =
      P ^ 4 * quarticMargin v b V W 1 (Q / P) := by
    unfold quarticMargin projectionBound
    field_simp [ne_of_gt hP]
  rw [hid]
  exact mul_nonneg (by positivity) hnorm

/-- The complete homogeneous inequality (20), including both orderings of
the two gradient norms and all allowable spectral defects. -/
theorem quartic_bound {v b V W P Q : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hsum : V + W ≤ 2 - v - b) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (27 / 128) * v * b * (P + Q) ^ 2 *
        (projectionBound v b V W * P ^ 2 + projectionBound b v W V * Q ^ 2) +
      (3 / 4) * v * b * (P + Q) *
        ((1 - 3 * (v - b) / 8) * P ^ 3 + (1 - 3 * (b - v) / 8) * Q ^ 3) ≤
      (67 / 50 + 27 * v * b / 100) * (P ^ 2 + Q ^ 2) * (b * P ^ 2 + v * Q ^ 2) := by
  suffices hm : 0 ≤ quarticMargin v b V W P Q by
    unfold quarticMargin at hm
    linarith
  by_cases hzero : P = 0 ∧ Q = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simp [quarticMargin]
  rcases le_total Q P with hQP | hPQ
  · have hPpos : 0 < P := by
      by_contra h
      have : P = 0 := by linarith
      have : Q = 0 := by linarith
      exact hzero ⟨‹P = 0›, this⟩
    exact ordered_margin_nonneg hv hb hW hsum hPpos hQ hQP
  · have hQpos : 0 < Q := by
      by_contra h
      have : Q = 0 := by linarith
      have : P = 0 := by linarith
      exact hzero ⟨this, ‹Q = 0›⟩
    rw [← quarticMargin_swap]
    exact ordered_margin_nonneg hb hv hV (by linarith) hQpos hP hPQ

/-- The quartic estimate after the two nonradial energy defects have been
removed. Here `P² = 5 |p|² / 3` and `Q² = 5 |q|² / 3`; the factor `9/25`
converts back to the gradient energies in the combined integrand. -/
theorem zero_defect_quartic_bound {v b V W P Q : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hsum : V + W ≤ 2 - v - b) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (3 / 10) * (P + Q) *
        ((1 - 3 * (v - b) / 8) * P ^ 3 + (1 - 3 * (b - v) / 8) * Q ^ 3) +
      (27 / 320) * (P + Q) ^ 2 *
        (projectionBound v b V W * P ^ 2 + projectionBound b v W V * Q ^ 2) -
      (2 / 5) * (17 / 10) * (P ^ 2 + Q ^ 2) * (P ^ 2 / v + Q ^ 2 / b) ≤
      -(2 / 5 - 3 * v * b / 10) * (9 / 25) *
        (P ^ 2 + Q ^ 2) * (P ^ 2 / v + Q ^ 2 / b) := by
  have hm : 0 ≤ quarticMargin v b V W P Q := by
    unfold quarticMargin
    exact sub_nonneg.mpr (quartic_bound hv hb hV hW hsum hP hQ)
  have hmul := mul_nonneg (show 0 ≤ 2 / (5 * v * b) by positivity) hm
  have hid : 2 / (5 * v * b) * quarticMargin v b V W P Q =
      -(2 / 5 - 3 * v * b / 10) * (9 / 25) *
        (P ^ 2 + Q ^ 2) * (P ^ 2 / v + Q ^ 2 / b) -
      ((3 / 10) * (P + Q) *
        ((1 - 3 * (v - b) / 8) * P ^ 3 + (1 - 3 * (b - v) / 8) * Q ^ 3) +
      (27 / 320) * (P + Q) ^ 2 *
        (projectionBound v b V W * P ^ 2 + projectionBound b v W V * Q ^ 2) -
      (2 / 5) * (17 / 10) * (P ^ 2 + Q ^ 2) * (P ^ 2 / v + Q ^ 2 / b)) := by
    unfold quarticMargin
    field_simp
    ring
  rw [hid] at hmul
  linarith

end

end PositiveEinsteinFour.Quartic

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_QuarticEnergy
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full scalar quartic estimate, with both energy and spectral defects. -/

namespace PositiveEinsteinFour.QuarticEnergy

open Energy Quartic

noncomputable section

/-- The normalized spectral parameter controls the actual projection cost. -/
theorem projectionCoefficient_le
    {v b r σ ρ W : ℝ}
    (hv : 0 ≤ v) (hr : 1 ≤ r) (hr2 : r ≤ 2) (hvr : v * r ≤ 2)
    (hσ : σ = (3 * r - r ^ 3) / 2) (hρ : ρ ^ 2 = 1 - σ ^ 2) :
    projectionCoefficient v (b + W) σ ρ ≤ projectionBound v b (v * r - v) W := by
  have h := spectral_defect_bound hv hr hr2 hvr hσ hρ
  unfold projectionCoefficient projectionBound
  linarith

/-- At zero energy defects the expression in (19) is exactly the scalar form
bounded by the homogeneous inequality (20). -/
theorem energy_zero_defect_identity
    (v b V W H Hb P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    quarticEnergy v b (P ^ 2) (Q ^ 2)
      (projectionBound v b V W) (projectionBound b v W V) H Hb (P ^ 2) (Q ^ 2) =
    (3 / 10) * (P + Q) *
      ((1 - 3 * (v - b) / 8) * P ^ 3 + (1 - 3 * (b - v) / 8) * Q ^ 3) +
    (27 / 320) * (P + Q) ^ 2 *
      (projectionBound v b V W * P ^ 2 + projectionBound b v W V * Q ^ 2) -
    (2 / 5) * (17 / 10) * (P ^ 2 + Q ^ 2) * (P ^ 2 / v + Q ^ 2 / b) := by
  have hk : (Real.sqrt (3 / 5 : ℝ)) ^ 2 = (3 / 5 : ℝ) := Real.sq_sqrt (by norm_num)
  unfold quarticEnergy gradientSum scalarWeight
  rw [Real.sqrt_sq hP, Real.sqrt_sq hQ]
  ring_nf
  rw [hk]
  ring

/-- Increasing the fixed radial coefficients increases the zero-defect
energy expression. The remaining coefficients are irrelevant at zero defect. -/
theorem energy_zero_defect_mono_coefficients
    (v b H Hb P Q g gb g' gb' : ℝ) (hg : g ≤ g') (hgb : gb ≤ gb') :
    quarticEnergy v b (P ^ 2) (Q ^ 2) g gb H Hb (P ^ 2) (Q ^ 2) ≤
      quarticEnergy v b (P ^ 2) (Q ^ 2) g' gb' H Hb (P ^ 2) (Q ^ 2) := by
  have hc : 0 ≤ (9 / 64 : ℝ) * (gradientSum (P ^ 2) (Q ^ 2)) ^ 2 := by positivity
  have h := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_right hg (sq_nonneg P))
      (mul_le_mul_of_nonneg_right hgb (sq_nonneg Q))) hc
  unfold quarticEnergy
  simp only [sub_self, mul_zero, add_zero]
  linarith

/-- The entire right side of equation (19) is bounded by the negative quartic
term, retaining the actual spectral coefficients and arbitrary nonnegative
energy defects. The normalized eigenvalue parameters supply the spectral
restrictions rather than assuming axial curvature. -/
theorem quartic_energy_bound
    {v b r s σ τ ρ χ P Q e f : ℝ}
    (hv : 0 < v) (hb : 0 < b)
    (hr : 1 ≤ r) (hr2 : r ≤ 2) (hs : 1 ≤ s) (hs2 : s ≤ 2)
    (hspectral : v * r + b * s ≤ 2)
    (hσ : σ = (3 * r - r ^ 3) / 2) (hρ : ρ ^ 2 = 1 - σ ^ 2)
    (hτ : τ = (3 * s - s ^ 3) / 2) (hχ : χ ^ 2 = 1 - τ ^ 2)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (he : P ^ 2 ≤ e) (hf : Q ^ 2 ≤ f) :
    quarticEnergy v b (P ^ 2) (Q ^ 2)
      (projectionCoefficient v (b * s) σ ρ) (projectionCoefficient b (v * r) τ χ)
      (defectCoefficient v (b * s)) (defectCoefficient b (v * r)) e f ≤
    -(2 / 5 - 3 * v * b / 10) * (9 / 25) *
      (P ^ 2 + Q ^ 2) * (P ^ 2 / v + Q ^ 2 / b) := by
  have hvx : v ≤ v * r := by nlinarith
  have hby : b ≤ b * s := by nlinarith
  have hV : 0 ≤ v * r - v := by linarith
  have hW : 0 ≤ b * s - b := by linarith
  have hsum : (v * r - v) + (b * s - b) ≤ 2 - v - b := by linarith
  have hg := projectionCoefficient_le (b := b) (W := b * s - b)
    hv.le hr hr2 (by nlinarith) hσ hρ
  have hgb := projectionCoefficient_le (b := v) (W := v * r - v)
    hb.le hs hs2 (by nlinarith) hτ hχ
  rw [show b + (b * s - b) = b * s by ring] at hg
  rw [show v + (v * r - v) = v * r by ring] at hgb
  calc
    _ ≤ quarticEnergy v b (P ^ 2) (Q ^ 2)
        (projectionCoefficient v (b * s) σ ρ) (projectionCoefficient b (v * r) τ χ)
        (defectCoefficient v (b * s)) (defectCoefficient b (v * r)) (P ^ 2) (Q ^ 2) :=
      remove_energy_defects_from_spectral_bounds _ _ hv hb hvx hby hspectral
        (sq_nonneg P) (sq_nonneg Q) he hf
    _ ≤ quarticEnergy v b (P ^ 2) (Q ^ 2)
        (projectionBound v b (v * r - v) (b * s - b))
        (projectionBound b v (b * s - b) (v * r - v))
        (defectCoefficient v (b * s)) (defectCoefficient b (v * r)) (P ^ 2) (Q ^ 2) :=
      energy_zero_defect_mono_coefficients _ _ _ _ _ _ _ _ _ _ hg hgb
    _ = _ := energy_zero_defect_identity _ _ _ _ _ _ _ _ hP hQ
    _ ≤ _ := zero_defect_quartic_bound hv hb hV hW hsum hP hQ

/-- The same estimate in the squared gradient variables of the combined
integrand: `a = |p|²` and `d = |q|²`. -/
theorem quartic_energy_bound_gradient
    {v b r s σ τ ρ χ a d e f : ℝ}
    (hv : 0 < v) (hb : 0 < b)
    (hr : 1 ≤ r) (hr2 : r ≤ 2) (hs : 1 ≤ s) (hs2 : s ≤ 2)
    (hspectral : v * r + b * s ≤ 2)
    (hσ : σ = (3 * r - r ^ 3) / 2) (hρ : ρ ^ 2 = 1 - σ ^ 2)
    (hτ : τ = (3 * s - s ^ 3) / 2) (hχ : χ ^ 2 = 1 - τ ^ 2)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (he : (5 / 3) * a ≤ e) (hf : (5 / 3) * d ≤ f) :
    quarticEnergy v b ((5 / 3) * a) ((5 / 3) * d)
      (projectionCoefficient v (b * s) σ ρ) (projectionCoefficient b (v * r) τ χ)
      (defectCoefficient v (b * s)) (defectCoefficient b (v * r)) e f ≤
      -(2 / 5 - 3 * v * b / 10) * (a + d) * (a / v + d / b) := by
  have hP : 0 ≤ (5 / 3 : ℝ) * a := by positivity
  have hQ : 0 ≤ (5 / 3 : ℝ) * d := by positivity
  have h := quartic_energy_bound (e := e) (f := f) hv hb hr hr2 hs hs2 hspectral hσ hρ hτ hχ
    (Real.sqrt_nonneg ((5 / 3) * a)) (Real.sqrt_nonneg ((5 / 3) * d))
    (by rwa [Real.sq_sqrt hP]) (by rwa [Real.sq_sqrt hQ])
  rw [Real.sq_sqrt hP, Real.sq_sqrt hQ] at h
  calc
    _ ≤ -(2 / 5 - 3 * v * b / 10) * (9 / 25) *
        ((5 / 3) * a + (5 / 3) * d) * (((5 / 3) * a) / v + ((5 / 3) * d) / b) := h
    _ = _ := by ring

end
end PositiveEinsteinFour.QuarticEnergy

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_QuarticClosed
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quartic estimate at vanishing Weyl blocks, with totalized division. -/

namespace PositiveEinsteinFour.QuarticClosed

open Energy QuarticEnergy

noncomputable section

/-- Cancellation at a vanished first block is exact under Lean's totalized
field division, including at zero norm. -/
theorem quarticEnergy_axis (x b τ χ d f g H : ℝ) :
    quarticEnergy x b 0 ((5 / 3) * d) g (projectionCoefficient b x τ χ)
      H (defectCoefficient b x) 0 f = axisEnergy x b τ χ d f := by
  unfold quarticEnergy axisEnergy
  simp only [Real.sqrt_zero, mul_zero, add_zero, zero_add, sub_zero,
    zero_div]

/-- The quartic bound on a single surviving block. A continuous approach through
positive two-block data supplies the endpoint, including maximal spectral
curvature. No division by the vanished block is used. -/
theorem quartic_axis_bound
    {b s τ χ d f : ℝ} (hb : 0 < b) (hs : 1 ≤ s) (hs2 : s ≤ 2)
    (hbs : b * s ≤ 2) (hτ : τ = (3 * s - s ^ 3) / 2)
    (hχ : χ ^ 2 = 1 - τ ^ 2) (hd : 0 ≤ d) (hf : (5 / 3) * d ≤ f) :
    axisEnergy 0 b τ χ d f ≤ -(2 / 5 : ℝ) * d * (d / b) := by
  let F : ℝ → ℝ := fun t => axisEnergy t ((1 - t) * b) τ χ d f +
    (2 / 5 - 3 * t * ((1 - t) * b) / 10) * d * (d / ((1 - t) * b))
  have hden : (1 - (0 : ℝ)) * b ≠ 0 := by simpa using ne_of_gt hb
  have hcont : ContinuousAt F 0 := by
    dsimp [F, axisEnergy, scalarWeight, projectionCoefficient, defectCoefficient]
    fun_prop (disch := assumption)
  have hpoint : ∀ t ∈ Set.Ioo (0 : ℝ) 1, F t ≤ 0 := by
    intro t ht
    have htb : 0 < (1 - t) * b := mul_pos (by linarith [ht.2]) hb
    have hspec : t * 1 + ((1 - t) * b) * s ≤ 2 := by
      have h := mul_le_mul_of_nonneg_left hbs (show 0 ≤ 1 - t by linarith [ht.2])
      nlinarith [ht.1]
    have h := quartic_energy_bound_gradient (r := 1) (σ := 1) (ρ := 0) (a := 0)
      (e := 0) (f := f) ht.1 htb (by norm_num) (by norm_num)
      hs hs2 hspec (by norm_num) (by norm_num) hτ hχ (by norm_num) hd
      (by norm_num) hf
    norm_num only [mul_zero, mul_one] at h
    rw [quarticEnergy_axis] at h
    dsimp [F]
    norm_num only [zero_add, zero_div, mul_zero, sub_zero] at h
    linarith
  have hzero : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, by norm_num⟩
  have hlimit := ContinuousWithinAt.closure_le hzero hcont.continuousWithinAt
    continuousWithinAt_const hpoint
  dsimp [F] at hlimit
  norm_num only [sub_zero, one_mul, zero_mul, sub_zero] at hlimit
  linarith

/-- The quartic estimate on the closed spectral domain. The two zero-set
hypotheses encode exactly that a vanished curvature block has zero derivative
energy there; they remove every singular divided term by its zero numerator. -/
theorem quartic_energy_bound_closed
    {v b r s σ τ ρ χ a d e f : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hr : 1 ≤ r) (hr2 : r ≤ 2) (hs : 1 ≤ s) (hs2 : s ≤ 2)
    (hspectral : v * r + b * s ≤ 2)
    (hσ : σ = (3 * r - r ^ 3) / 2) (hρ : ρ ^ 2 = 1 - σ ^ 2)
    (hτ : τ = (3 * s - s ^ 3) / 2) (hχ : χ ^ 2 = 1 - τ ^ 2)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (he : (5 / 3) * a ≤ e) (hf : (5 / 3) * d ≤ f)
    (hve : v = 0 → e = 0) (hbf : b = 0 → f = 0) :
    quarticEnergy v b ((5 / 3) * a) ((5 / 3) * d)
      (projectionCoefficient v (b * s) σ ρ) (projectionCoefficient b (v * r) τ χ)
      (defectCoefficient v (b * s)) (defectCoefficient b (v * r)) e f ≤
      -(2 / 5 - 3 * v * b / 10) * (a + d) * (a / v + d / b) := by
  by_cases hvzero : v = 0
  · have hezero := hve hvzero
    have hazero : a = 0 := by nlinarith
    subst v
    subst e
    subst a
    by_cases hbzero : b = 0
    · have hfzero := hbf hbzero
      have hdzero : d = 0 := by nlinarith
      subst b
      subst f
      subst d
      simp [quarticEnergy, gradientSum]
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
      have haxis := quartic_axis_bound hbpos hs hs2 (by simpa using hspectral) hτ hχ hd hf
      simp only [mul_zero, zero_mul, zero_add, sub_zero, zero_div]
      rw [quarticEnergy_axis]
      exact haxis
  · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hvzero)
    by_cases hbzero : b = 0
    · have hfzero := hbf hbzero
      have hdzero : d = 0 := by nlinarith
      subst b
      subst f
      subst d
      have haxis := quartic_axis_bound hvpos hr hr2 (by simpa using hspectral) hσ hρ ha he
      simp only [mul_zero, zero_mul, add_zero, sub_zero, zero_div]
      rw [quarticEnergy_swap, quarticEnergy_axis]
      exact haxis
    · exact quartic_energy_bound_gradient hvpos (lt_of_le_of_ne hb (Ne.symm hbzero))
        hr hr2 hs hs2 hspectral hσ hρ hτ hχ ha hd he hf

end
end PositiveEinsteinFour.QuarticClosed

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates00
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-!
# Assembly of the scalar integrand bounds

The quartic, quadratic, and potential estimates bound the scalar integrand.
The tangent pairing is the real inner product.
-/

namespace PositiveEinsteinFour

open Energy QuarticEnergy QuarticClosed Quadratic Boundary Potential

noncomputable section

/-- Every scalar estimate needed for the final coupled bound, including all
zero sets, follows from the concrete polynomial certificates. -/
theorem reduced_integrand_bound_oai
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v b r s σ τ ρ χ e f : ℝ} (p q : E)
    (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hr : 1 ≤ r) (hr2 : r ≤ 2) (hs : 1 ≤ s) (hs2 : s ≤ 2)
    (hspectral : v * r + b * s ≤ 2)
    (hσ : σ = (3 * r - r ^ 3) / 2) (hρ : ρ ^ 2 = 1 - σ ^ 2)
    (hτ : τ = (3 * s - s ^ 3) / 2) (hχ : χ ^ 2 = 1 - τ ^ 2)
    (he : (5 / 3) * ‖p‖ ^ 2 ≤ e) (hf : (5 / 3) * ‖q‖ ^ 2 ≤ f)
    (hve : v = 0 → e = 0) (hbf : b = 0 → f = 0) :
    reducedIntegrand v b r s σ τ ρ χ e f p q ≤
      -couplingCoefficient v b * (‖p‖ ^ 2 + ‖q‖ ^ 2) *
        (‖p‖ ^ 2 / v + ‖q‖ ^ 2 / b) +
      2 * theta v b * (normWeight v * ‖p‖ ^ 2 + normWeight b * ‖q‖ ^ 2) -
      theta v b ^ 2 / couplingCoefficient v b := by
  have hvx : v ≤ v * r := by nlinarith
  have hby : b ≤ b * s := by nlinarith
  have hsum : v + b ≤ 2 := by linarith
  have hpzero : v = 0 → p = 0 := by
    intro h
    have hn : ‖p‖ = 0 := by nlinarith [hve h, norm_nonneg p, sq_nonneg ‖p‖]
    exact norm_eq_zero.mp hn
  have hqzero : b = 0 → q = 0 := by
    intro h
    have hn : ‖q‖ = 0 := by nlinarith [hbf h, norm_nonneg q, sq_nonneg ‖q‖]
    exact norm_eq_zero.mp hn
  have h4 := quartic_energy_bound_closed hv hb hr hr2 hs hs2 hspectral hσ hρ hτ hχ
    (sq_nonneg ‖p‖) (sq_nonneg ‖q‖) he hf hve hbf
  have hc : 2 / 5 - 3 * v * b / 10 = couplingCoefficient v b := by
    unfold couplingCoefficient
    ring
  rw [hc] at h4
  have h2 := hilbert_quadratic_bound_closed hv hb hsum p q hpzero hqzero
  have hσupper : σ ≤ 1 := by
    have hfac : 1 - σ = (r - 1) ^ 2 * (r + 2) / 2 := by rw [hσ]; ring
    have hh : 0 ≤ (r - 1) ^ 2 * (r + 2) / 2 := by positivity
    linarith
  have hτupper : τ ≤ 1 := by
    have hfac : 1 - τ = (s - 1) ^ 2 * (s + 2) / 2 := by rw [hτ]; ring
    have hh : 0 ≤ (s - 1) ^ 2 * (s + 2) / 2 := by positivity
    linarith
  have hδ : 0 ≤ 2 - v - b := by linarith
  have hvdefect := spectral_potential_defect_bound hv hr hr2 hδ (by linarith) hσ
  have hbdefect := spectral_potential_defect_bound hb hs hs2 hδ (by linarith) hτ
  have h0 := zeroOrder_bound hv hb hsum hσupper hτupper hvdefect hbdefect
  unfold reducedIntegrand
  convert add_le_add (add_le_add h4 h2) h0 using 1
  all_goals try with_reducible_and_instances rfl
  ring

end
end PositiveEinsteinFour
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PositiveEinsteinFour.reduced_integrand_bound_oai.{u_1} := @OAI.PositiveEinsteinFour.reduced_integrand_bound_oai.{u_1}
