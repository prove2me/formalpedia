-- Prove2me | solution 1 for LatinQuarter.cyclic_isLatin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:13.630222+00:00
-- url     : https://prove2.me/submissions/5b62a6dd-4d2c-4ded-811e-de082340123d

module
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Definitions.Def_LeanPool_LatinQuarter_Cyclic

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
namespace LatinQuarter
theorem _root_.solution (n : ℕ) (hn : 0 < n) : IsLatin (cyclic n) := by
  let : NeZero n := ⟨by omega⟩
  exact ⟨fun r => (Equiv.addLeft r).bijective, fun c => (Equiv.addRight c).bijective⟩
end LatinQuarter
