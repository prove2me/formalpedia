-- Prove2me | solution 1 for NashWilliams.cr_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:17:48.294736+00:00
-- url     : https://prove2.me/submissions/89e062a0-a5d0-4da2-a8bd-e3199d4e3136

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution (p : V × V) (A B C : Finset V) :
    cr p ((A \ B) \ C) + cr p ((B \ A) \ C) + cr p ((C \ A) \ B) + cr p (A ∩ B ∩ C) +
      2 * (if (p.1 ∈ A ∩ B ∩ C ∧ p.2 ∉ A ∪ B ∪ C) ∨ (p.2 ∈ A ∩ B ∩ C ∧ p.1 ∉ A ∪ B ∪ C)
        then 1 else 0) ≤ cr p A + cr p B + cr p C := by
  unfold cr
  by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.1 ∈ B <;> by_cases h3 : p.1 ∈ C <;>
    by_cases h4 : p.2 ∈ A <;> by_cases h5 : p.2 ∈ B <;> by_cases h6 : p.2 ∈ C <;> simp [*]
end NashWilliams
