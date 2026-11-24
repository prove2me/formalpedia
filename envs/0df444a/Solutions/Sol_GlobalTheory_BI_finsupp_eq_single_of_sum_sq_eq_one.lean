-- Prove2me | solution 1 for GlobalTheory.BI.finsupp_eq_single_of_sum_sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:09.147057+00:00
-- url     : https://prove2.me/submissions/bb15957e-63d8-4462-9c0f-8d4ea7497dfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterIrreducibleExpansionNormSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution {α : Type} (c : α →₀ ℤ)
    (h : (c.sum fun _ m => m ^ 2) = 1) :
    ∃ a, c.support = {a} ∧ (c a = 1 ∨ c a = -1) := by
  simp only [Finsupp.sum] at h
  have hge : ∀ b ∈ c.support, (1 : ℤ) ≤ c b ^ 2 := by
    intro b hb
    have hb' : c b ≠ 0 := Finsupp.mem_support_iff.mp hb
    rcases lt_or_gt_of_ne hb' with hlt | hgt <;> nlinarith
  have hle : (c.support.card : ℤ) ≤ 1 := by
    calc (c.support.card : ℤ) = ∑ _b ∈ c.support, (1 : ℤ) := by simp
      _ ≤ ∑ b ∈ c.support, c b ^ 2 := Finset.sum_le_sum hge
      _ = 1 := h
  have hne : c.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at h
    exact zero_ne_one h
  have hcard : c.support.card = 1 := by
    have := hne.card_pos
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  refine ⟨a, ha, ?_⟩
  rw [ha, Finset.sum_singleton] at h
  have h1 : c a ≤ 1 := by nlinarith
  have h2 : -1 ≤ c a := by nlinarith
  have h3 : c a ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  omega
end GlobalTheory.BI
