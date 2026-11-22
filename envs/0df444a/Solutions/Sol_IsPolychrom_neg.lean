-- Prove2me | solution 1 for IsPolychrom.neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:34:58.467369+00:00
-- url     : https://prove2.me/submissions/698a1eb7-12cd-475d-8f5e-db97d2828464

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
theorem _root_.solution [DecidableEq G] (h : IsPolychrom S χ) :
    IsPolychrom (-S) (fun g ↦ χ (-g)) := by
  intro n g
  obtain ⟨a, ha, hg⟩ := h (-n) g
  refine ⟨-a, by simpa, ?_⟩
  simpa only [neg_add, neg_neg]
end IsPolychrom
