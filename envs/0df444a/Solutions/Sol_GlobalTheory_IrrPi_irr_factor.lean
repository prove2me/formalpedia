-- Prove2me | solution 1 for GlobalTheory.IrrPi.irr_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:55.247607+00:00
-- url     : https://prove2.me/submissions/9e162d4c-6793-487f-8f54-3864c459dc58

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
import Theorems.Thm_GlobalTheory_IrrPi_irr_one
import Theorems.Thm_GlobalTheory_IrrPi_irr_mulSingle

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
    [∀ i, Finite (G i)] {χ : (∀ i, G i) → ℂ} (h : IsIrrChar ℂ ℂ χ) (x : ∀ i, G i) :
    χ x = χ 1 * ∏ i, (χ (Pi.mulSingle i (x i)) / χ 1) := by
  obtain ⟨n, hn, h1⟩ := irr_one h
  have h0 : χ 1 ≠ 0 := by rw [h1]; exact_mod_cast hn
  have key : ∀ s : Finset ι, χ (fun j => if j ∈ s then x j else 1) =
      χ 1 * ∏ i ∈ s, (χ (Pi.mulSingle i (x i)) / χ 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, if_false, Finset.prod_empty, mul_one]
      rfl
    | insert i s hi ih =>
      have e : (fun j => if j ∈ insert i s then x j else 1) =
          Pi.mulSingle i (x i) * (fun j => if j ∈ s then x j else 1) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [hi]
        · simp [Pi.mulSingle_eq_of_ne hj, hj]
      have := irr_mulSingle h i (x i) (fun j => if j ∈ s then x j else 1) (by simp [hi])
      rw [e, Finset.prod_insert hi]
      apply mul_left_cancel₀ h0
      rw [this, ih]
      field_simp
  simpa using key Finset.univ
end GlobalTheory.IrrPi
