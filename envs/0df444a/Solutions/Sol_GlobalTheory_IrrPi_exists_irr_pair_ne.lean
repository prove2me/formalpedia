-- Prove2me | solution 1 for GlobalTheory.IrrPi.exists_irr_pair_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:34:50.477576+00:00
-- url     : https://prove2.me/submissions/bbe456c2-2463-4e81-a4cf-f60bef20c917

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
import Theorems.Thm_GlobalTheory_BI_pair_eq_zero_of_isIrrChar_ne
import Theorems.Thm_GlobalTheory_BI_pair_self_of_isIrrChar_algClosed
import Theorems.Thm_GlobalTheory_BI_virt_expand


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
theorem _root_.solution {G : Type} [Group G] [Finite G] {φ : G → ℂ} (h : φ ∈ Virt ℂ ℂ G)
    (h1 : φ 1 ≠ 0) : ∃ ψ, IsIrrChar ℂ ℂ ψ ∧ pair φ ψ ≠ 0 := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨c, hc, hφ, -⟩ := virt_expand G φ h
  have hne : c.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    rintro rfl
    rw [hφ] at h1
    simp at h1
  obtain ⟨ψ, hψ⟩ := hne
  refine ⟨ψ, hc ψ hψ, ?_⟩
  have e : pair φ ψ = ∑ χ ∈ c.support, (c χ : ℂ) * pair χ ψ := by
    rw [hφ]
    simp only [pair, finsum_eq_sum_of_fintype, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
      zsmul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [Pi.mul_apply, Pi.intCast_apply]
    ring
  rw [e, Finset.sum_eq_single ψ]
  · rw [pair_self_of_isIrrChar_algClosed ℂ G ψ (hc ψ hψ), mul_one]
    exact_mod_cast Finsupp.mem_support_iff.1 hψ
  · intro b hb hbψ
    rw [pair_eq_zero_of_isIrrChar_ne G b ψ (hc b hb) (hc ψ hψ) hbψ, mul_zero]
  · intro h
    exact absurd hψ h
end GlobalTheory.IrrPi
