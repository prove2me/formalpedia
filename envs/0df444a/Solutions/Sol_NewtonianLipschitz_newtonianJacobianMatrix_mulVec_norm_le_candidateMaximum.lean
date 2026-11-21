-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_mulVec_norm_le_candidateMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:05:26.288295+00:00
-- url     : https://prove2.me/submissions/27aaefde-db88-4198-990b-06b619c5b510

module
public import Definitions.Def_NewtonianLipschitz_JacobianCartesianBound
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorAction
public import Theorems.Thm_NewtonianLipschitz_matrix3_mulVec_coordinate_abs_le_rowSum
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_nonneg
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_rowSum_le_candidateMaximum_norm
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
theorem _root_.solution
    (μ : ℝ) (x h : Vec3)
    (hμ : 0 ≤ μ) (hx : x ≠ 0) :
    ‖newtonianJacobianMatrix μ x *ᵥ h‖ ≤
      ((1 / ‖x‖ ^ 3) * (μ * candidateMaximum)) * ‖h‖ := by
  have hfactor :
      0 ≤ (1 / ‖x‖ ^ 3) * (μ * candidateMaximum) :=
    mul_nonneg (by positivity)
      (mul_nonneg hμ candidateMaximum_nonneg)
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg hfactor (norm_nonneg h))).2
  intro i
  have hcoord :
      |(newtonianJacobianMatrix μ x *ᵥ h) i| ≤
        ((1 / ‖x‖ ^ 3) * (μ * candidateMaximum)) * ‖h‖ := by
    calc
      |(newtonianJacobianMatrix μ x *ᵥ h) i|
        ≤ (∑ j : Fin 3,
            |newtonianJacobianMatrix μ x i j|) * ‖h‖ :=
          matrix3_mulVec_coordinate_abs_le_rowSum
            (newtonianJacobianMatrix μ x) h i
      _ ≤ ((1 / ‖x‖ ^ 3) * (μ * candidateMaximum)) * ‖h‖ :=
        mul_le_mul_of_nonneg_right
          (newtonianJacobianMatrix_rowSum_le_candidateMaximum_norm
            μ x i hμ hx) (norm_nonneg h)
  simpa only [Real.norm_eq_abs] using hcoord
end NewtonianLipschitz
