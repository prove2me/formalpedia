-- Prove2me | solution 1 for NashWilliams.lv_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:27:19.654084+00:00
-- url     : https://prove2.me/submissions/f513c0cc-8f3e-43d9-a156-be71100d25e3

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
    (S : Finset V) :
    lv (u, v) b S ≤ lv p (if p.2 = s then b else !b) S + lv q (if q.1 = s then b else !b) S := by
  obtain ⟨hp | hp, hu⟩ := hp <;> obtain ⟨hq | hq, hv⟩ := hq <;> subst hp hq <;>
    cases b <;> by_cases hs : s ∈ S <;> by_cases hu' : u ∈ S <;> by_cases hv' : v ∈ S <;>
    simp [lv, Leaves, *]
end NashWilliams
