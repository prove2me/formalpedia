-- Prove2me | solution 1 for Mader.ndeg_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:40.573456+00:00
-- url     : https://prove2.me/submissions/a5c01098-cd24-4153-b4fa-ba522ffd00c6

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*}
variable (G : SimpleGraph V)
namespace Mader
theorem _root_.solution {S T : Finset V} {v : V} (h : ∀ w ∈ S, G.Adj v w → w ∈ T) :
    ndeg G S v ≤ T.card := by
  classical
  unfold ndeg
  apply card_le_card
  intro w hw
  rw [mem_filter] at hw
  exact h w hw.1 hw.2
end Mader
