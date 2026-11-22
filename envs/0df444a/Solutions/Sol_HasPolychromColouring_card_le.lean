-- Prove2me | solution 1 for HasPolychromColouring.card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:38:20.924178+00:00
-- url     : https://prove2.me/submissions/e5223c48-605f-407c-8b48-74d59f49dbc5

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring
import Theorems.Thm_IsPolychrom_card_le

set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset
namespace HasPolychromColouring
theorem _root_.solution [Fintype K] (h : HasPolychromColouring K S) :
    Fintype.card K ≤ #S :=
  have ⟨_, hχ⟩ := h
  hχ.card_le
end HasPolychromColouring
