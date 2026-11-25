-- Prove2me | solution 2 for Menger.Aux.R.of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:44:40.948816+00:00
-- url     : https://prove2.me/submissions/e1ec8378-e8f5-4182-af94-3149d0e7f371

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
