-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.unitAxis_fderiv_exists_attaining_direction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:12:46.508207+00:00
-- url     : https://prove2.me/submissions/e044ebd2-ad2b-4d8f-9269-5e074c6e81c0

module
public import Definitions.Def_NewtonianLipschitz_DerivativeCoefficientMinimality
public import Definitions.Def_NewtonianLipschitz_DerivativeAttainingDirection
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_eq_jacobianMatrix
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_fderiv_opNorm_eq_candidateMaximum
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_gravitationalParameter_eq_one
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_nonneg
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_criticalDiagonal_cartesian_norm_eq_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_matrix3_exists_rowSum_attaining_direction
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
    ∃ h : Vec3, ‖h‖ ≤ 1 ∧
      ‖(fderiv ℝ NewtonianPointSource.unitAxis.accelerationField
        (normalizedVector candidateCriticalPoint candidateCriticalPoint)) h‖ =
          candidateMaximum := by
  let c := NewtonianPointSource.unitAxis
  let x := normalizedVector candidateCriticalPoint candidateCriticalPoint
  let A := newtonianJacobianMatrix c.gravitationalParameter x
  have hnorm : ‖x‖ = (1 : ℝ) :=
    criticalDiagonal_cartesian_norm_eq_one
  have hx : x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  obtain ⟨h, hh, hrowAction⟩ :=
    matrix3_exists_rowSum_attaining_direction A 0
  have hrow :
      (∑ j : Fin 3, |A 0 j|) = candidateMaximum := by
    change (∑ j : Fin 3,
      |newtonianJacobianMatrix c.gravitationalParameter x 0 j|) =
        candidateMaximum
    rw [NewtonianPointSource.unitAxis_gravitationalParameter_eq_one]
    exact newtonianJacobianMatrix_critical_firstRow_eq_candidateMaximum
  have haction :
      (fderiv ℝ c.accelerationField x) h = A *ᵥ h := by
    rw [c.accelerationField_fderiv_eq_jacobianMatrix x h hx]
  have hcomponent : (A *ᵥ h) 0 ≤ ‖A *ᵥ h‖ := by
    have habs : (A *ᵥ h) 0 ≤ |(A *ᵥ h) 0| :=
      le_abs_self _
    have hpi : |(A *ᵥ h) 0| ≤ ‖A *ᵥ h‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (A *ᵥ h) 0)
    exact habs.trans hpi
  have hlower :
      candidateMaximum ≤
        ‖(fderiv ℝ c.accelerationField x) h‖ := by
    calc
      candidateMaximum = ∑ j : Fin 3, |A 0 j| := hrow.symm
      _ = (A *ᵥ h) 0 := hrowAction.symm
      _ ≤ ‖A *ᵥ h‖ := hcomponent
      _ = ‖(fderiv ℝ c.accelerationField x) h‖ := by
        rw [haction]
  have hoperator :
      ‖fderiv ℝ c.accelerationField x‖ = candidateMaximum :=
    NewtonianPointSource.unitAxis_fderiv_opNorm_eq_candidateMaximum
  have hupper :
      ‖(fderiv ℝ c.accelerationField x) h‖ ≤
        candidateMaximum := by
    calc
      ‖(fderiv ℝ c.accelerationField x) h‖
          ≤ ‖fderiv ℝ c.accelerationField x‖ * ‖h‖ :=
            (fderiv ℝ c.accelerationField x).le_opNorm h
      _ ≤ candidateMaximum * 1 := by
        rw [hoperator]
        exact mul_le_mul_of_nonneg_left hh candidateMaximum_nonneg
      _ = candidateMaximum := mul_one _
  exact ⟨h, hh, le_antisymm hupper hlower⟩
end NewtonianPointSource
end NewtonianLipschitz
