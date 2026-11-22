-- Prove2me | solution 1 for IsPolychrom.subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:35:12.291794+00:00
-- url     : https://prove2.me/submissions/03268b27-9956-4a92-8d01-c0b455861812

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring

set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset
namespace IsPolychrom
theorem _root_.solution {S' : Finset G} (hχ : IsPolychrom S' χ) (hS : S' ⊆ S) :
    IsPolychrom S χ := by
  classical exact isPolychrom_iff_surjOn.2 fun n ↦ (hχ.surjOn n).trans (by gcongr)
end IsPolychrom
