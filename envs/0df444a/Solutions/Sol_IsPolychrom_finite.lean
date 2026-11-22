-- Prove2me | solution 1 for IsPolychrom.finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:38:10.524347+00:00
-- url     : https://prove2.me/submissions/f4b46672-1208-48e0-80cb-452aab0b1e25

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
theorem _root_.solution (hχ : IsPolychrom S χ) :
    Finite K := by classical exact hχ.fintype.finite
end IsPolychrom
