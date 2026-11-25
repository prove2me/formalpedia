-- Prove2me | solution 1 for Menger.Aux.R.of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:07:58.34595+00:00
-- url     : https://prove2.me/submissions/de6d39a6-a131-42b6-8634-1f5504917a1e

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
theorem _root_.solution {H : SimpleGraph V} {A Y : Finset V} {w : V} (hw : w ∈ A) (hY : w ∉ Y) :
    R H A Y w :=
  ⟨w, hw, Walk.nil, by simpa using hY⟩
end R
end Menger.Aux
