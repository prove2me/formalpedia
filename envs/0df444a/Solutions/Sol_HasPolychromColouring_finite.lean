-- Prove2me | solution 1 for HasPolychromColouring.finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:45:46.389943+00:00
-- url     : https://prove2.me/submissions/e1d01817-6da9-4d18-a5ab-42af0c30b4cc

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring
import Theorems.Thm_IsPolychrom_finite

set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset
namespace HasPolychromColouring
theorem _root_.solution (h : HasPolychromColouring K S) :
    Finite K :=
  have ⟨_, hχ⟩ := h
  hχ.finite
end HasPolychromColouring
