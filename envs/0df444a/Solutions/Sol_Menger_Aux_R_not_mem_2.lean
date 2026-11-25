-- Prove2me | solution 2 for Menger.Aux.R.not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:48:10.925932+00:00
-- url     : https://prove2.me/submissions/e0d9a413-5004-4760-8710-98fc0cf48807

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
namespace R
theorem _root_.solution {H : SimpleGraph V} {A Y : Finset V} {w : V} (h : R H A Y w) : w ∉ Y := by
  obtain ⟨a, -, p, hp⟩ := h
  exact hp w p.end_mem_support
end R
end Menger.Aux
