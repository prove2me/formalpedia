-- Prove2me | solution 1 for IsPolychrom.card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:36:12.077831+00:00
-- url     : https://prove2.me/submissions/0607591e-43c2-4f30-802e-a88ec701e414

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
theorem _root_.solution [Fintype K] (hχ : IsPolychrom S χ) :
    Fintype.card K ≤ #S :=
  card_le_card_of_surjOn χ (by classical simpa using hχ.surjOn 0)
end IsPolychrom
