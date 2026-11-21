-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.unitAxis_fderiv_opNorm_ge_candidateMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:59:31.867773+00:00
-- url     : https://prove2.me/submissions/1ba7af80-e3ab-433a-b212-39c3c14fcd2e

module
public import Definitions.Def_NewtonianLipschitz_JacobianSharpWitness
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorWitness
public import Theorems.Thm_NewtonianLipschitz_matrix3_exists_rowSum_attaining_direction
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_eq_jacobianMatrix
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_gravitationalParameter_eq_one
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_criticalDiagonal_cartesian_norm_eq_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_critical_firstRow_eq_candidateMaximum
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
namespace NewtonianPointSource
theorem _root_.solution :
    candidateMaximum ≤
      ‖fderiv ℝ NewtonianPointSource.unitAxis.accelerationField
        (normalizedVector candidateCriticalPoint candidateCriticalPoint)‖ := by
  let c := NewtonianPointSource.unitAxis
  let x := normalizedVector candidateCriticalPoint candidateCriticalPoint
  let A := newtonianJacobianMatrix c.gravitationalParameter x
  have hnorm : ‖x‖ = (1 : ℝ) :=
    criticalDiagonal_cartesian_norm_eq_one
  have hx : x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  obtain ⟨h, hh, heq⟩ :=
    matrix3_exists_rowSum_attaining_direction A 0
  have hrow : (∑ j : Fin 3, |A 0 j|) = candidateMaximum := by
    change (∑ j : Fin 3,
      |newtonianJacobianMatrix c.gravitationalParameter x 0 j|) =
        candidateMaximum
    rw [NewtonianPointSource.unitAxis_gravitationalParameter_eq_one]
    exact newtonianJacobianMatrix_critical_firstRow_eq_candidateMaximum
  have hcoordinate : (A *ᵥ h) 0 ≤ ‖A *ᵥ h‖ := by
    have habs : (A *ᵥ h) 0 ≤ |(A *ᵥ h) 0| := le_abs_self _
    have hpi : |(A *ᵥ h) 0| ≤ ‖A *ᵥ h‖ := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (A *ᵥ h) 0)
    exact habs.trans hpi
  calc
    candidateMaximum = (A *ᵥ h) 0 := by rw [heq, hrow]
    _ ≤ ‖A *ᵥ h‖ := hcoordinate
    _ = ‖(fderiv ℝ c.accelerationField x) h‖ := by
      rw [c.accelerationField_fderiv_eq_jacobianMatrix x h hx]
    _ ≤ ‖fderiv ℝ c.accelerationField x‖ * ‖h‖ :=
      (fderiv ℝ c.accelerationField x).le_opNorm h
    _ ≤ ‖fderiv ℝ c.accelerationField x‖ * 1 :=
      mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ = ‖fderiv ℝ c.accelerationField x‖ := by ring
end NewtonianPointSource
end NewtonianLipschitz
