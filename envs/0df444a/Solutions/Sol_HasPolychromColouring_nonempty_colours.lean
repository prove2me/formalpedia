-- Prove2me | solution 1 for HasPolychromColouring.nonempty_colours
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:45:36.414596+00:00
-- url     : https://prove2.me/submissions/8d872dad-cccc-4298-9ca9-83506ce728a1

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
namespace HasPolychromColouring
theorem _root_.solution (h : HasPolychromColouring K S) : Nonempty K := by
  obtain ⟨χ, hχ⟩ := h
  exact ⟨χ 0⟩
end HasPolychromColouring
