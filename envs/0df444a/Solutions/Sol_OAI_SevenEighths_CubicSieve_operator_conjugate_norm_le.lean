-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.operator_conjugate_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:42:00.925426+00:00
-- url     : https://prove2.me/submissions/a7ffeea7-0760-4c83-92ee-e741c57f21ca

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator
import Theorems.Thm_OAI_SevenEighths_CubicSieve_operator_apply
import Theorems.Thm_OAI_SevenEighths_CubicSieve_conjugateVector_apply
import Theorems.Thm_OAI_SevenEighths_CubicSieve_norm_conjugateVector
import Theorems.Thm_OAI_SevenEighths_CubicSieve_operator_conjugate_apply
attribute [local simp] OAI.SevenEighths.CubicSieve.operator_apply
attribute [local simp] OAI.SevenEighths.CubicSieve.conjugateVector_apply
attribute [local simp] OAI.SevenEighths.CubicSieve.norm_conjugateVector

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [DecidableEq m]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [operator_conjugate_apply, norm_conjugateVector]
  simpa only [norm_conjugateVector] using (operator A).le_opNorm (conjugateVector x)
end OAI.SevenEighths.CubicSieve
