-- Prove2me | solution 1 for GlobalTheory.IrrPi.irr_mulSingle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:16:17.871434+00:00
-- url     : https://prove2.me/submissions/16e68a63-8d83-473c-beb4-54810f33fbc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingSelfIrreducibleAlgClos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_StarVirtualCharacterEqApplyInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterIrreducibleExpansionNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrrCharOneMulFinsumConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleCharacterOfProduct
import Theorems.Thm_GlobalTheory_IrrPi_isChar_of_irr
import Theorems.Thm_GlobalTheory_irrChar_one_mul_finsum_conj_mul
import Theorems.Thm_GlobalTheory_isChar_restrict_conj_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.IrrPi
namespace GlobalTheory.IrrPi
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] {χ : (∀ i, G i) → ℂ} (h : IsIrrChar ℂ ℂ χ) (i : ι) (a : G i) (y : ∀ i, G i)
    (hy : y i = 1) : χ 1 * χ (Pi.mulSingle i a * y) = χ (Pi.mulSingle i a) * χ y := by
  have := Fintype.ofFinite (∀ i, G i)
  have h1 := irrChar_one_mul_finsum_conj_mul _ χ h (Pi.mulSingle i a) y
  have hc := (isChar_restrict_conj_one ℂ ℂ _ χ (isChar_of_irr h)).2.1
  have h2 : ∀ k : ∀ i, G i, χ (k * Pi.mulSingle i a * k⁻¹ * y) = χ (Pi.mulSingle i a * y) := by
    intro k
    rw [← hc (Pi.mulSingle i a * y) (Pi.mulSingle i (k i)⁻¹)]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp [hy]
    · simp [Pi.mulSingle_eq_of_ne hj]
  simp only [h2, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  rw [Nat.card_eq_fintype_card] at h1
  have hN : (Fintype.card (∀ i, G i) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  apply mul_left_cancel₀ hN
  rw [← h1]
  ring
end GlobalTheory.IrrPi
