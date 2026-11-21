-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_any_safe_axis_tangent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:09:32.166954+00:00
-- url     : https://prove2.me/submissions/10a68d67-e5a9-4541-b2da-e837b27b61fc

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialFirstAxis
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialAllAxes
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_second_safe_axis_tangent_columns_le
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_third_safe_axis_tangent_columns_le
public import Theorems.Thm_NewtonianLipschitz_matrix3_mulVec_tangent_one_norm_le
public import Theorems.Thm_NewtonianLipschitz_matrix3_mulVec_tangent_two_norm_le
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_eq_jacobianMatrix
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_cons
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_nil
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_matrix3_mulVec_tangent_zero_norm_le
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_first_safe_axis_tangent_columns_le
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_one
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_two
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_zero
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_one
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_two
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_zero
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_cons
attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_nil
attribute [local simp] NewtonianLipschitz.coordinateAbs_apply
attribute [local simp] NewtonianLipschitz.cycleIndex_one
attribute [local simp] NewtonianLipschitz.cycleIndex_two
attribute [local simp] NewtonianLipschitz.cycleIndex_zero
attribute [local simp] NewtonianLipschitz.cycleVec_one
attribute [local simp] NewtonianLipschitz.cycleVec_two
attribute [local simp] NewtonianLipschitz.cycleVec_zero
attribute [local simp] NewtonianLipschitz.normalizedVector_one
attribute [local simp] NewtonianLipschitz.normalizedVector_two
attribute [local simp] NewtonianLipschitz.normalizedVector_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.swapYZIndex_one
attribute [local simp] NewtonianLipschitz.swapYZIndex_two
attribute [local simp] NewtonianLipschitz.swapYZIndex_zero
attribute [local simp] NewtonianLipschitz.swapYZVec_one
attribute [local simp] NewtonianLipschitz.swapYZVec_two
attribute [local simp] NewtonianLipschitz.swapYZVec_zero
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x h : Vec3) (d : ℝ)
    (hd : 0 < d) (i : Fin 3)
    (hx : d ≤ |x i|) (hh : h i = 0) :
    ‖(fderiv ℝ c.accelerationField x) h‖ ≤
      ((1 / d ^ 3) *
        (c.gravitationalParameter * (5 / 4 : ℝ))) * ‖h‖ := by
  have hx_ne : x ≠ 0 := by
    intro hz
    have hz_i := congrArg (fun q : Vec3 => q i) hz
    simp only [Pi.zero_apply] at hz_i
    rw [hz_i, abs_zero] at hx
    linarith
  rw [c.accelerationField_fderiv_eq_jacobianMatrix x h hx_ne]
  let B : ℝ :=
    (1 / d ^ 3) * (c.gravitationalParameter * (5 / 4 : ℝ))
  have hB : 0 ≤ B :=
    mul_nonneg (by positivity)
      (mul_nonneg c.gravitationalParameter_nonneg (by norm_num))
  change ‖newtonianJacobianMatrix c.gravitationalParameter x *ᵥ h‖ ≤
    B * ‖h‖
  fin_cases i
  · exact matrix3_mulVec_tangent_zero_norm_le
      (newtonianJacobianMatrix c.gravitationalParameter x)
      h hh B hB (fun k =>
        newtonianJacobianMatrix_first_safe_axis_tangent_columns_le
          c.gravitationalParameter d x k
          c.gravitationalParameter_nonneg hd hx)
  · exact matrix3_mulVec_tangent_one_norm_le
      (newtonianJacobianMatrix c.gravitationalParameter x)
      h hh B hB (fun k =>
        newtonianJacobianMatrix_second_safe_axis_tangent_columns_le
          c.gravitationalParameter d x k
          c.gravitationalParameter_nonneg hd hx)
  · exact matrix3_mulVec_tangent_two_norm_le
      (newtonianJacobianMatrix c.gravitationalParameter x)
      h hh B hB (fun k =>
        newtonianJacobianMatrix_third_safe_axis_tangent_columns_le
          c.gravitationalParameter d x k
          c.gravitationalParameter_nonneg hd hx)
end NewtonianPointSource
end NewtonianLipschitz
