-- Prove2me | solution 1 for HasPolychromColouring.of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:36:27.42179+00:00
-- url     : https://prove2.me/submissions/0c5c9a16-fd2f-4010-8971-a5cd7871dae4

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
theorem _root_.solution {K₁ K₂ : Type*}
    (h₁ : HasPolychromColouring K₁ S) {f : K₁ → K₂} (hf : f.Surjective) :
    HasPolychromColouring K₂ S :=
  have ⟨χ₁, hχ₁⟩ := h₁
  ⟨f ∘ χ₁, by classical exact isPolychrom_iff_surjOn.2 fun n ↦ hf.surjOn.comp (hχ₁.surjOn n)⟩
end HasPolychromColouring
