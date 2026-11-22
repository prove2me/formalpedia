-- Prove2me | solution 1 for HasPolychromColouring.subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:36:26.980155+00:00
-- url     : https://prove2.me/submissions/fa709d3d-1642-40de-8b8a-d770ab8b1b7d

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring
import Theorems.Thm_IsPolychrom_subset

set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset
namespace HasPolychromColouring
theorem _root_.solution {S' : Finset G} (h : HasPolychromColouring K S') (hS : S' ⊆ S) :
    HasPolychromColouring K S :=
  have ⟨χ, hχ⟩ := h
  ⟨χ, hχ.subset hS⟩
end HasPolychromColouring
