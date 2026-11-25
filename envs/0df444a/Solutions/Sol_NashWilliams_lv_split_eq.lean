-- Prove2me | solution 1 for NashWilliams.lv_split_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:27:22.729801+00:00
-- url     : https://prove2.me/submissions/16ac2c39-f1a1-4016-80d2-fe448432f396

module
public import Definitions.Def_NashWilliamsLib_Mader
public import Definitions.Def_NashWilliamsLib_Splitting
public import Definitions.Def_NashWilliamsLib_Orientation

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
omit [DecidableEq ι]
namespace NashWilliams
theorem _root_.solution {s u v : V} {p q : V × V} (hp : Joins s u p) (hq : Joins s v q) (b : Bool)
    {X : Finset V} (h : (s ∈ X ∧ u ∉ X ∧ v ∉ X) ∨ (s ∉ X ∧ u ∈ X ∧ v ∈ X)) :
    lv (u, v) b X + 1 =
      lv p (if p.2 = s then b else !b) X + lv q (if q.1 = s then b else !b) X := by
  obtain ⟨hp | hp, hu⟩ := hp <;> obtain ⟨hq | hq, hv⟩ := hq <;> subst hp hq <;>
    cases b <;> rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp [lv, Leaves, *]
end NashWilliams
