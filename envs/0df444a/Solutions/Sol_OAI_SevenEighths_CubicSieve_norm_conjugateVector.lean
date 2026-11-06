-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.norm_conjugateVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:35:30.510046+00:00
-- url     : https://prove2.me/submissions/e4599070-b089-4176-99e3-5c41b953a2a5

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator
import Theorems.Thm_OAI_SevenEighths_CubicSieve_operator_apply
import Theorems.Thm_OAI_SevenEighths_CubicSieve_conjugateVector_apply
attribute [local simp] OAI.SevenEighths.CubicSieve.operator_apply
attribute [local simp] OAI.SevenEighths.CubicSieve.conjugateVector_apply

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [DecidableEq n]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution (x : EuclideanSpace ℂ n) :
    ‖conjugateVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, conjugateVector_apply, norm_star]
end OAI.SevenEighths.CubicSieve
