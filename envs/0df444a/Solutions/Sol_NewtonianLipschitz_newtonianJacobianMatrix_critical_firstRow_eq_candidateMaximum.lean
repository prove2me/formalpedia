-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_critical_firstRow_eq_candidateMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:57:51.638864+00:00
-- url     : https://prove2.me/submissions/feb93d21-8c0c-4753-bfe1-0b6313bb4686

module
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorNorm
public import Definitions.Def_NewtonianLipschitz_JacobianSharpWitness
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_diagonal_firstRow_eq_coefficient
public import Theorems.Thm_NewtonianLipschitz_candidateCriticalPoint_spec
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_eq
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
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
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix (1 : ℝ)
        (normalizedVector candidateCriticalPoint candidateCriticalPoint)
          0 j|) = candidateMaximum := by
  obtain ⟨ht0, ht1, _⟩ := candidateCriticalPoint_spec
  have ht_nonneg : 0 ≤ candidateCriticalPoint := by linarith
  have ht_le_one : candidateCriticalPoint ≤ 1 := by linarith
  have hrow :=
    newtonianJacobianMatrix_diagonal_firstRow_eq_coefficient
      1 candidateCriticalPoint (by norm_num) ht_nonneg ht_le_one
  simpa only [one_mul, candidateMaximum_eq] using hrow
end NewtonianLipschitz
