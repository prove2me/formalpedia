-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_norm_le_seven_of_clearance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:01:42.949387+00:00
-- url     : https://prove2.me/submissions/cb9d72c8-ff4e-4295-896b-987aa6ec0219

module
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
public import Definitions.Def_NewtonianLipschitz_ImprovedBounds
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_norm_le_cauchy_clearance
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_inverse_cube_parameter_le_of_clearance
public import Theorems.Thm_NewtonianLipschitz_cartesian_norm_le_euclideanRadius
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_physical_norm
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_norm_le_two_cartesian_norm
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
      (7 * M / d ^ 3) * ‖h‖ := by
  let r : ℝ := euclideanRadius x
  have hr : 0 < r := lt_of_lt_of_le hd hclear
  have hcoef : 0 ≤ 3 * c.gravitationalParameter / r ^ 5 := by
    exact div_nonneg
      (mul_nonneg (by norm_num) c.gravitationalParameter_nonneg)
      (pow_nonneg (le_of_lt hr) _)
  have hnormx : ‖x‖ ≤ r := cartesian_norm_le_euclideanRadius x
  have hnormh : ‖toPhysicalVec3 h‖ ≤ 2 * ‖h‖ :=
    toPhysicalVec3_norm_le_two_cartesian_norm h
  have hcauchy :
      ‖(fderiv ℝ c.accelerationField x) h‖ ≤
        (c.gravitationalParameter / r ^ 3) * ‖h‖ +
          (3 * c.gravitationalParameter / r ^ 5) *
            (‖toPhysicalVec3 x‖ * ‖toPhysicalVec3 h‖) * ‖x‖ := by
    simpa only [r] using
      c.accelerationField_fderiv_norm_le_cauchy_clearance
        x h r c.gravitationalParameter hx hr le_rfl le_rfl
  have hstep1 :
      (3 * c.gravitationalParameter / r ^ 5) *
          (r * ‖toPhysicalVec3 h‖) * ‖x‖ ≤
        (3 * c.gravitationalParameter / r ^ 5) *
          (r * (2 * ‖h‖)) * ‖x‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    apply mul_le_mul_of_nonneg_left _ hcoef
    exact mul_le_mul_of_nonneg_left hnormh (le_of_lt hr)
  have hstep2 :
      (3 * c.gravitationalParameter / r ^ 5) *
          (r * (2 * ‖h‖)) * ‖x‖ ≤
        (3 * c.gravitationalParameter / r ^ 5) *
          (r * (2 * ‖h‖)) * r := by
    apply mul_le_mul_of_nonneg_left hnormx
    exact mul_nonneg hcoef
      (mul_nonneg (le_of_lt hr)
        (mul_nonneg (by norm_num) (norm_nonneg h)))
  have hcancel :
      (3 * c.gravitationalParameter / r ^ 5) *
          (r * (2 * ‖h‖)) * r =
        (6 * c.gravitationalParameter / r ^ 3) * ‖h‖ := by
    field_simp [ne_of_gt hr]
    ring
  have hexact :
      ‖(fderiv ℝ c.accelerationField x) h‖ ≤
        (7 * c.gravitationalParameter / r ^ 3) * ‖h‖ := by
    calc
      _ ≤ (c.gravitationalParameter / r ^ 3) * ‖h‖ +
          (3 * c.gravitationalParameter / r ^ 5) *
            (‖toPhysicalVec3 x‖ * ‖toPhysicalVec3 h‖) * ‖x‖ := hcauchy
      _ = (c.gravitationalParameter / r ^ 3) * ‖h‖ +
          (3 * c.gravitationalParameter / r ^ 5) *
            (r * ‖toPhysicalVec3 h‖) * ‖x‖ := by
          rw [← euclideanRadius_eq_physical_norm]
      _ ≤ (c.gravitationalParameter / r ^ 3) * ‖h‖ +
          (3 * c.gravitationalParameter / r ^ 5) *
            (r * (2 * ‖h‖)) * ‖x‖ :=
          add_le_add (le_refl _) hstep1
      _ ≤ (c.gravitationalParameter / r ^ 3) * ‖h‖ +
          (3 * c.gravitationalParameter / r ^ 5) *
            (r * (2 * ‖h‖)) * r :=
          add_le_add (le_refl _) hstep2
      _ = (7 * c.gravitationalParameter / r ^ 3) * ‖h‖ := by
          rw [hcancel]
          ring
  have hmu :
      c.gravitationalParameter / r ^ 3 ≤ M / d ^ 3 :=
    c.inverse_cube_parameter_le_of_clearance x d M hd hclear hM
  calc
    ‖(fderiv ℝ c.accelerationField x) h‖ ≤
        (7 * c.gravitationalParameter / r ^ 3) * ‖h‖ := hexact
    _ = (7 * (c.gravitationalParameter / r ^ 3)) * ‖h‖ := by ring
    _ ≤ (7 * (M / d ^ 3)) * ‖h‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmu (by norm_num))
        (norm_nonneg h)
    _ = (7 * M / d ^ 3) * ‖h‖ := by ring
end NewtonianPointSource
end NewtonianLipschitz
