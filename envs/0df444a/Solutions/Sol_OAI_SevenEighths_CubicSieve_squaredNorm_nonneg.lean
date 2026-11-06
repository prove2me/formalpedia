-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.squaredNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:57:59.327407+00:00
-- url     : https://prove2.me/submissions/8740be50-b01a-4e95-9070-1118f70f2a5c

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
