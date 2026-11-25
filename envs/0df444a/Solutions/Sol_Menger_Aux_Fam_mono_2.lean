-- Prove2me | solution 2 for Menger.Aux.Fam.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:44:44.465798+00:00
-- url     : https://prove2.me/submissions/d5ba04af-88d3-4b77-b231-125f04b35384

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
namespace Fam
theorem _root_.solution {G G' : SimpleGraph V} (hle : G ≤ G') {A B : Finset V} {k : ℕ}
    (h : Fam G A B k) : Fam G' A B k := by
  obtain ⟨P, hP, hd⟩ := h
  refine ⟨fun i => ⟨(P i).1, (P i).2.1, (P i).2.2.mapLe hle⟩, fun i => ?_, fun i j hij => ?_⟩
  · simp only [Walk.support_mapLe_eq_support, Walk.isPath_mapLe]
    exact hP i
  · simp only [Walk.support_mapLe_eq_support]
    exact hd i j hij
end Fam
end Menger.Aux
