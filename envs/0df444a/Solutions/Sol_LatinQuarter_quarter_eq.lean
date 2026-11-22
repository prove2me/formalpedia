-- Prove2me | solution 1 for LatinQuarter.quarter_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:12.504604+00:00
-- url     : https://prove2.me/submissions/7faa1f4d-ca69-4eb3-89e4-fddb474fc9f5

module
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Definitions.Def_LeanPool_LatinQuarter_Budget

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators
namespace LatinQuarter
theorem _root_.solution (n : ℕ) : n * n / 4 = (n / 2) * (n - n / 2) := by
  have hn : n = 2 * (n / 2) + n % 2 := by omega
  have hk : n / 2 ≤ n := by omega
  have hsub : n - n / 2 + n / 2 = n := Nat.sub_add_cancel hk
  have he : n * n = 4 * ((n / 2) * (n - n / 2)) + n % 2 := by
    have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hm with hm | hm <;> rw [hm] at hn ⊢ <;> nlinarith
  omega
end LatinQuarter
