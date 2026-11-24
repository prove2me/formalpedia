-- Prove2me | solution 1 for GlobalTheory.CuspGL.PsiPrimitive.finsum_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:04:00.424839+00:00
-- url     : https://prove2.me/submissions/0cff89b1-9adb-4e28-956b-d8bd354f0625

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEqFinsumPsiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumPrimitiveEndClassFunctionRestrictMixedSubspacStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyTransversalSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.PsiPrimitive
open Classical
namespace GlobalTheory.CuspGL.PsiPrimitive
theorem _root_.solution {α : Type} [Fintype α] (p : α → Prop) (f : {a // p a} → ℂ) :
    ∑ᶠ x, f x = ∑ a, if h : p a then f ⟨a, h⟩ else 0 := by
  rw [finsum_eq_sum_of_fintype, ← Fintype.sum_subtype_add_sum_subtype p]
  have h1 : ∀ i : {a // p a}, (if h : p i.1 then f ⟨i.1, h⟩ else 0) = f i := fun i => by
    rw [dif_pos i.2]
  have h2 : ∀ i : {a // ¬ p a}, (if h : p i.1 then f ⟨i.1, h⟩ else 0) = 0 := fun i => by
    rw [dif_neg i.2]
  simp only [h1, h2, Finset.sum_const_zero, add_zero]
end GlobalTheory.CuspGL.PsiPrimitive
