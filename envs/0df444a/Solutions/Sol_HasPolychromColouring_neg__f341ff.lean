-- Prove2me | solution 1 for HasPolychromColouring.neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:36:31.811246+00:00
-- url     : https://prove2.me/submissions/14bae690-839f-4267-a37a-d7f14a4d4da1

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring
import Theorems.Thm_IsPolychrom_neg

set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset
namespace HasPolychromColouring
theorem _root_.solution [DecidableEq G] (h : HasPolychromColouring K S) :
    HasPolychromColouring K (-S) := by
  obtain ⟨χ, hχ⟩ := h
  exact ⟨fun g ↦ χ (-g), hχ.neg⟩
end HasPolychromColouring
