-- Prove2me | solution 1 for GlobalTheory.irrChar_pi_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:05:26.363683+00:00
-- url     : https://prove2.me/submissions/335fc499-0320-45c6-8546-aa456a6d12cc

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
import Theorems.Thm_GlobalTheory_IrrPi_pair_prod
import Theorems.Thm_GlobalTheory_IrrPi_irr_one
import Theorems.Thm_GlobalTheory_IrrPi_irr_factor
import Theorems.Thm_GlobalTheory_IrrPi_exists_irr_pair_ne
import Theorems.Thm_GlobalTheory_IrrPi_prod_mem_virt
import Theorems.Thm_GlobalTheory_BI_irr_of_norm_one
import Theorems.Thm_GlobalTheory_BI_pair_eq_zero_of_isIrrChar_ne
import Theorems.Thm_GlobalTheory_BI_pair_self_of_isIrrChar_algClosed
import Theorems.Thm_GlobalTheory_CuspGL_star_virt_eq_inv
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
open GlobalTheory
open IrrPi
namespace GlobalTheory
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (χ : (∀ i, G i) → ℂ), IsIrrChar ℂ ℂ χ → ∃ ψ : ∀ i, G i → ℂ, (∀ i, IsIrrChar ℂ ℂ (ψ i)) ∧ ∀ x, χ x = ∏ i, ψ i (x i) := by
  intro ι _ G _ _ χ h
  classical
  obtain ⟨n, hn, h1⟩ := irr_one h
  have h0 : χ 1 ≠ 0 := by rw [h1]; exact_mod_cast hn
  have hφ : ∀ i, ∃ ψ, IsIrrChar ℂ ℂ ψ ∧ pair (fun a : G i => χ (Pi.mulSingle i a)) ψ ≠ 0 := by
    intro i
    refine exists_irr_pair_ne (AddSubgroup.subset_closure
      ((isChar_restrict_conj_one ℂ ℂ _ χ (isChar_of_irr h)).1 _ (MonoidHom.mulSingle G i))) ?_
    simpa using h0
  choose ψ hψ hp using hφ
  refine ⟨ψ, hψ, ?_⟩
  have hV := prod_mem_virt ψ fun i => AddSubgroup.subset_closure (isChar_of_irr (hψ i))
  set Ψ : (∀ i, G i) → ℂ := fun x => ∏ i, ψ i (x i) with hΨ
  have hN : (Nat.card (∀ i, G i) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hnorm : ∑ᶠ g, Ψ g * star (Ψ g) = (Nat.card (∀ i, G i) : ℂ) := by
    have : pair Ψ Ψ = 1 := by
      rw [hΨ, pair_prod]
      exact Finset.prod_eq_one fun i _ => pair_self_of_isIrrChar_algClosed ℂ _ _ (hψ i)
    simp only [star_virt_eq_inv _ Ψ hV]
    unfold pair at this
    field_simp at this
    exact this
  have hpair : pair χ Ψ ≠ 0 := by
    have e : pair χ Ψ = χ 1 * pair (fun x : ∀ i, G i => ∏ i, χ (Pi.mulSingle i (x i)) / χ 1) Ψ := by
      unfold pair
      have := Fintype.ofFinite (∀ i, G i)
      simp only [finsum_eq_sum_of_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [irr_factor h x]
      ring
    rw [e, hΨ, pair_prod (fun i (a : G i) => χ (Pi.mulSingle i a) / χ 1) ψ]
    refine mul_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    have e2 : pair (fun a => χ (Pi.mulSingle i a) / χ 1) (ψ i) =
        pair (fun a : G i => χ (Pi.mulSingle i a)) (ψ i) / χ 1 := by
      unfold pair
      have := Fintype.ofFinite (G i)
      simp only [finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [e2]
    exact div_ne_zero (hp i) h0
  rcases (irr_of_norm_one _ Ψ hV hnorm).1 with hI | hI
  · by_contra hne
    exact hpair (pair_eq_zero_of_isIrrChar_ne _ χ Ψ h hI fun e => hne fun x => congrFun e x)
  · exfalso
    choose m hm hm1 using fun i => irr_one (hψ i)
    obtain ⟨k, hk, hk1⟩ := irr_one hI
    have : ((k + ∏ i, m i : ℕ) : ℂ) = 0 := by
      push_cast
      rw [← hk1]
      simp [hΨ, hm1]
    have : k + ∏ i, m i = 0 := by exact_mod_cast this
    omega
end GlobalTheory
