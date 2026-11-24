-- Prove2me | solution 1 for GlobalTheory.CuspGL.psi_of_finrank_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:42:49.996346+00:00
-- url     : https://prove2.me/submissions/3fe5930e-5470-432d-a6ee-a4b5daae2fc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyOfIrreduci
import Theorems.Thm_GlobalTheory_CuspGL_psi_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution {F : Type} [Field F] (s : F[X] → ℂ) (hs : IsAdditive s)
    (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V)
    (h : Module.finrank F V = 0) : psi s V g = 0 := by
  have hsub : Subsingleton V := Module.finrank_zero_iff.mp h
  have h1 : LinearMap.charpoly g = 1 := by
    apply (LinearMap.charpoly_monic g).natDegree_eq_zero.mp
    rw [LinearMap.charpoly_natDegree, h]
  have h0 : s 1 = 0 := by
    have := hs 1 1 monic_one monic_one
    rw [one_mul] at this
    linear_combination -this
  have : IsEmpty {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} :=
    ⟨fun W => W.2.1 (Subsingleton.elim _ _)⟩
  rw [psi_eq, h1, h0, finsum_of_isEmpty, sub_zero]
end GlobalTheory.CuspGL
