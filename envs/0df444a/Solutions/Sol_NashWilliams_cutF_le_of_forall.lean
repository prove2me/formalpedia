-- Prove2me | solution 1 for NashWilliams.cutF_le_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:40:02.083606+00:00
-- url     : https://prove2.me/submissions/014f6209-41f8-47f4-956c-8032ae4eb4ae

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
theorem _root_.solution {ends : ι → V × V} {F : Finset ι} {S S' : Finset V}
    (h : ∀ i ∈ F, ((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S) → ((ends i).1 ∈ S') ≠ ((ends i).2 ∈ S')) :
    cutF ends F S ≤ cutF ends F S' := by
  unfold cutF
  exact Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, h i hi.1 hi.2⟩
end NashWilliams
