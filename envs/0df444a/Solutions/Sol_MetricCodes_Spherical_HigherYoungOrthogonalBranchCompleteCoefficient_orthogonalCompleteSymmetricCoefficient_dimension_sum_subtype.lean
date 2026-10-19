-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient.orthogonalCompleteSymmetricCoefficient_dimension_sum_subtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/39dc8296-1eab-44b7-a178-cec7d60029a5

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungOrthogonalBranchCompleteCoefficient_orthogonalCompleteSymmetricCoefficient_dimension_sum_Icc

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
namespace MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
theorem _root_.solution
    {n : ℕ} (hn : 2 ≤ n) {L U : ℕ} (hLU : L ≤ U) (shift : ℤ) :
    (∑ k : {k : Fin (U + 1) // L ≤ k.val},
      orthogonalCompleteSymmetricCoefficient (n - 1)
        ((k.val.val : ℤ) + shift)) =
      orthogonalCompleteSymmetricCoefficient n ((U : ℤ) + shift) -
        orthogonalCompleteSymmetricCoefficient n (((L : ℤ) - 1) + shift) := by
  classical
  let branchIndex (k : ℕ) (hk : k ∈ Finset.Icc L U) :
      {j : Fin (U + 1) // L ≤ j.val} :=
    ⟨⟨k, by have h := (Finset.mem_Icc.mp hk).2; omega⟩,
      (Finset.mem_Icc.mp hk).1⟩
  have hindex :
      (∑ k ∈ Finset.Icc L U,
        orthogonalCompleteSymmetricCoefficient (n - 1)
          ((k : ℤ) + shift)) =
        ∑ k : {k : Fin (U + 1) // L ≤ k.val},
          orthogonalCompleteSymmetricCoefficient (n - 1)
            ((k.val.val : ℤ) + shift) := by
    apply Finset.sum_bij branchIndex
    · intro k hk
      exact Finset.mem_univ _
    · intro k₁ hk₁ k₂ hk₂ heq
      exact congrArg (fun j : {j : Fin (U + 1) // L ≤ j.val} => j.val.val) heq
    · intro k hk
      have hmem : k.val.val ∈ Finset.Icc L U := by
        apply Finset.mem_Icc.mpr
        exact ⟨k.property, by have h := k.val.isLt; omega⟩
      refine ⟨k.val.val, hmem, ?_⟩
      apply Subtype.ext
      apply Fin.ext
      rfl
    · intro k hk
      rfl
  rw [← hindex]
  exact orthogonalCompleteSymmetricCoefficient_dimension_sum_Icc hn hLU shift
end MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
