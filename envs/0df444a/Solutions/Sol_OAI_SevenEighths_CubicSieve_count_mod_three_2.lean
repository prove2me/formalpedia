-- Prove2me | solution 2 for OAI.SevenEighths.CubicSieve.count_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:32.443851+00:00
-- url     : https://prove2.me/submissions/86d3fcfb-8ac1-441f-968e-30cc57120f17

import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Factorization
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators Classical
open UniqueFactorizationMonoid
noncomputable section
variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]

theorem solution (k : ℕ) :
    k = (if k % 3 = 1 then 1 else 0) +
      2 * (if k % 3 = 2 then 1 else 0) + 3 * (k / 3) := by
  split_ifs <;> omega
