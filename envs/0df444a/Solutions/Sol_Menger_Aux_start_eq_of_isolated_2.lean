-- Prove2me | solution 2 for Menger.Aux.start_eq_of_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:46:20.092849+00:00
-- url     : https://prove2.me/submissions/01398d0b-3223-4c5d-b91b-cf2ef32da02b

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
public import Theorems.Thm_Menger_Aux_Sep_symm

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}
namespace Menger.Aux
theorem _root_.solution {H : SimpleGraph V} {v : V} (hv : ∀ w, ¬ H.Adj v w) :
    ∀ {a b : V} (p : H.Walk a b), v ∈ p.support → a = v
  | _, _, .nil, h => by simp only [Walk.support_nil, List.mem_singleton] at h; exact h.symm
  | _, _, .cons h' q, h => by
    rw [Walk.support_cons, List.mem_cons] at h
    rcases h with h | h
    · exact h.symm
    · have := solution hv q h
      subst this
      exact absurd h'.symm (hv _)
end Menger.Aux
