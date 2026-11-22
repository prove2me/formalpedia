-- Prove2me | solution 1 for HasPolychromColouring.of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:38:24.187375+00:00
-- url     : https://prove2.me/submissions/bd6b2d8d-86b0-4d65-bbca-e9bf84d4b66c

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring
import Theorems.Thm_HasPolychromColouring_of_surjective

set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset
namespace HasPolychromColouring
theorem _root_.solution {K₁ K₂ : Type*} [Nonempty K₁]
    (h₁ : HasPolychromColouring K₂ S) {f : K₁ → K₂} (hf : f.Injective) :
    HasPolychromColouring K₁ S :=
  h₁.of_surjective (Function.invFun_surjective hf)
end HasPolychromColouring
