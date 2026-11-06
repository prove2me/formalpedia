-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.count_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:41:04.247312+00:00
-- url     : https://prove2.me/submissions/6aa7de3f-4677-476e-b751-fdc8c512d3ea

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
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution (k : ℕ) :
    k = (if k % 3 = 1 then 1 else 0) +
      2 * (if k % 3 = 2 then 1 else 0) + 3 * (k / 3) := by
  have h := Nat.mod_add_div k 3
  have hlt := Nat.mod_lt k (by decide : 0 < 3)
  split_ifs <;> omega
end OAI.SevenEighths.CubicSieve
