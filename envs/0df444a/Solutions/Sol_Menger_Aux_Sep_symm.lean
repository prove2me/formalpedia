-- Prove2me | solution 1 for Menger.Aux.Sep.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:08:08.126805+00:00
-- url     : https://prove2.me/submissions/fbb2b000-d602-4b0c-8af7-b785f8e1e18b

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
namespace Sep
theorem _root_.solution {G : SimpleGraph V} {A B X : Finset V} (h : Sep G A B X) : Sep G B A X := by
  intro b hb a ha p
  obtain ⟨x, hx, hxp⟩ := h a ha b hb p.reverse
  exact ⟨x, hx, by simpa using hxp⟩
end Sep
end Menger.Aux
