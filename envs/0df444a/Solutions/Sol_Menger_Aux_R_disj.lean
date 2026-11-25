-- Prove2me | solution 1 for Menger.Aux.R_disj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:08:10.467534+00:00
-- url     : https://prove2.me/submissions/ab0f6e9e-8985-4291-8329-c980ba33c566

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}
namespace Menger.Aux
theorem _root_.solution {H : SimpleGraph V} {A B Y : Finset V} (hY : Sep H A B Y) {w : V}
    (hA : R H A Y w) (hB : R H B Y w) : False := by
  obtain ⟨a, ha, p, hp⟩ := hA
  obtain ⟨b, hb, q, hq⟩ := hB
  obtain ⟨x, hx, hxs⟩ := hY a ha b hb (p.append q.reverse)
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hxs
  rcases hxs with h | h
  · exact hp x h hx
  · exact hq x h hx
end Menger.Aux
