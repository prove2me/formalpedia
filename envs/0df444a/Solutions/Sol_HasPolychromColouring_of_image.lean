-- Prove2me | solution 1 for HasPolychromColouring.of_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:39:28.508833+00:00
-- url     : https://prove2.me/submissions/c957769c-1cd7-453b-b2f6-db983c747957

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ

set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset
namespace HasPolychromColouring
theorem _root_.solution {H : Type*} [DecidableEq H] [AddCommGroup H]
    {F : Type*} [FunLike F G H] [AddHomClass F G H] (φ : F)
    (h : HasPolychromColouring K (S.image φ)) :
    HasPolychromColouring K S := by
  obtain ⟨χ', hχ'⟩ := h
  let χ (g : G) : K := χ' (φ g)
  suffices IsPolychrom S χ from ⟨_, this⟩
  intro g k
  obtain ⟨i, hi, hi'⟩ := hχ' (φ g) k
  aesop
end HasPolychromColouring
