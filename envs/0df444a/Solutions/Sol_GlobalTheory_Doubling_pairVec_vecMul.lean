-- Prove2me | solution 1 for GlobalTheory.Doubling.pairVec_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:44:02.980337+00:00
-- url     : https://prove2.me/submissions/703858da-7370-475a-9f2c-f4cce513d2e9

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : m ⊕ n ≃ ι)
variable [Fintype m] [Fintype n] [Fintype ι]
namespace GlobalTheory.Doubling
theorem _root_.solution (M : Matrix ι ι A) (x : m → A) (y : n → A) : pairVec e x y ᵥ* M =
    pairVec e (x ᵥ* (M.submatrix e e).toBlocks₁₁ + y ᵥ* (M.submatrix e e).toBlocks₂₁)
      (x ᵥ* (M.submatrix e e).toBlocks₁₂ + y ᵥ* (M.submatrix e e).toBlocks₂₂) := by
  funext j
  obtain ⟨i | i, rfl⟩ := e.surjective j <;>
    simp [vecMul, dotProduct, ← e.sum_comp, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]
end GlobalTheory.Doubling
