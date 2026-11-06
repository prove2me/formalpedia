-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.squaredNorm_reciprocity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:02.967452+00:00
-- url     : https://prove2.me/submissions/63cdd79f-7127-4b15-bfd9-331f69331f66

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator
import Theorems.Thm_OAI_SevenEighths_CubicSieve_operator_apply
import Theorems.Thm_OAI_SevenEighths_CubicSieve_conjugateVector_apply
import Theorems.Thm_OAI_SevenEighths_CubicSieve_norm_conjugateVector
import Theorems.Thm_OAI_SevenEighths_CubicSieve_squaredNorm_transpose
attribute [local simp] OAI.SevenEighths.CubicSieve.operator_apply
attribute [local simp] OAI.SevenEighths.CubicSieve.conjugateVector_apply
attribute [local simp] OAI.SevenEighths.CubicSieve.norm_conjugateVector

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution (A : Matrix m n ℂ) (B : Matrix n m ℂ)
    (hrecip : ∀ i j, A i j = B j i) : squaredNorm A = squaredNorm B := by
  have h : A = B.transpose := by ext i j; exact hrecip i j
  rw [h, squaredNorm_transpose]
end OAI.SevenEighths.CubicSieve
