-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_norm_le_of_clearance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:55:36.878321+00:00
-- url     : https://prove2.me/submissions/879699cd-995a-4c9b-ab59-6d79e1a6cbaf

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_inverse_cube_parameter_le_of_clearance
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_inverse_fifth_derivative_coefficient_le
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_full
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x h : Vec3) (d M : ℝ)
    (hx : x ≠ 0) (hd : 0 < d)
    (hclear : d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ M) :
    ‖(fderiv ℝ c.accelerationField x) h‖ ≤
      (M / d ^ 3) * ‖h‖ +
        (3 * M / d ^ 5) *
          abs (⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ) * ‖x‖ := by
  have hr : 0 < euclideanRadius x := lt_of_lt_of_le hd hclear
  have hmu5 : 0 ≤ 3 * c.gravitationalParameter /
      euclideanRadius x ^ 5 :=
    div_nonneg
      (mul_nonneg (by norm_num) c.gravitationalParameter_nonneg)
      (pow_nonneg (le_of_lt hr) _)
  have habs3 :
      |-(c.gravitationalParameter) / euclideanRadius x ^ 3| =
        c.gravitationalParameter / euclideanRadius x ^ 3 := by
    rw [abs_div, abs_neg,
      abs_of_nonneg c.gravitationalParameter_nonneg,
      abs_of_nonneg (pow_nonneg (le_of_lt hr) 3)]
  have hcoeff3 :=
    c.inverse_cube_parameter_le_of_clearance x d M hd hclear hM
  have hcoeff5 :=
    c.inverse_fifth_derivative_coefficient_le x d M hd hclear hM
  rw [c.accelerationField_fderiv_full x h hx]
  calc
    ‖(-(c.gravitationalParameter) / euclideanRadius x ^ 3) • h +
        ((3 * c.gravitationalParameter / euclideanRadius x ^ 5) *
          ⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ) • x‖ ≤
      ‖(-(c.gravitationalParameter) / euclideanRadius x ^ 3) • h‖ +
        ‖((3 * c.gravitationalParameter / euclideanRadius x ^ 5) *
          ⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ) • x‖ := norm_add_le _ _
    _ = (c.gravitationalParameter / euclideanRadius x ^ 3) * ‖h‖ +
        (3 * c.gravitationalParameter / euclideanRadius x ^ 5) *
          abs (⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ) * ‖x‖ := by
      simp only [norm_smul, Real.norm_eq_abs,
        habs3, abs_mul, abs_of_nonneg hmu5]
    _ ≤ (M / d ^ 3) * ‖h‖ +
          (3 * M / d ^ 5) *
            abs (⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ) * ‖x‖ := by
      have h3 :=
        mul_le_mul_of_nonneg_right hcoeff3 (norm_nonneg h)
      have hinner :
          0 ≤ abs (⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ) :=
        abs_nonneg _
      have h5 :
          (3 * c.gravitationalParameter / euclideanRadius x ^ 5) *
              abs (⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ) * ‖x‖ ≤
            (3 * M / d ^ 5) *
              abs (⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ) * ‖x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
        exact mul_le_mul_of_nonneg_right hcoeff5 hinner
      exact add_le_add h3 h5
end NewtonianPointSource
end NewtonianLipschitz
