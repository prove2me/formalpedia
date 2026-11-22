-- Prove2me | solution 1 for LatinQuarter.mem_cornerSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:06.411279+00:00
-- url     : https://prove2.me/submissions/998e4c03-574f-4e2c-a4ca-ad19ef66bc98

module
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Definitions.Def_LeanPool_LatinQuarter_Cyclic
public import Theorems.Thm_LatinQuarter_mem_completions
attribute [local simp] LatinQuarter.mem_completions



set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (r c : Fin n) :
    (r, c) ∈ cornerSet n ↔ r.val + c.val < n / 2 ∨
      n + n / 2 ≤ r.val + c.val := by simp [cornerSet]
end LatinQuarter
