-- Prove2me | solution 3 for OAI.SevenEighths.CubicSieve.squaredNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:15.334304+00:00
-- url     : https://prove2.me/submissions/8e691069-cc77-4f6e-b420-644801a8b525

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Blocks
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {a b n : Type*} [Fintype a] [Fintype b] [Fintype n]
  [DecidableEq n]
theorem solution (A : Matrix a n ℂ) : 0 ≤ squaredNorm A := by
  unfold squaredNorm
  positivity
