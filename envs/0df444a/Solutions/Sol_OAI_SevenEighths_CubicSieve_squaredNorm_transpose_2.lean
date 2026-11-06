-- Prove2me | solution 2 for OAI.SevenEighths.CubicSieve.squaredNorm_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:43:35.292524+00:00
-- url     : https://prove2.me/submissions/b5d08145-9e31-4d06-9ac9-552ec71c6365

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator
import Theorems.Thm_OAI_SevenEighths_CubicSieve_operator_conjugate_norm
import Theorems.Thm_OAI_SevenEighths_CubicSieve_operator_conjTranspose_norm

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution (A : Matrix m n ℂ) :
    squaredNorm A.transpose = squaredNorm A := by
  unfold squaredNorm
  have h := operator_conjugate_norm A.transpose
  change ‖operator A.conjTranspose‖ = ‖operator A.transpose‖ at h
  rw [operator_conjTranspose_norm] at h
  exact congrArg (fun x : ℝ => x ^ 2) h.symm
end OAI.SevenEighths.CubicSieve
