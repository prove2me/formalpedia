-- Prove2me | solution 1 for GlobalTheory.BadShare.ZCalc.zc_calc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:09:35.083914+00:00
-- url     : https://prove2.me/submissions/fcde1961-ec38-40d2-a0e9-46d27cc9cc52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Theorems.Thm_GlobalTheory_BadShare_ZCalc_character_inv
import Theorems.Thm_GlobalTheory_BadShare_ZCalc_op_zc
import Theorems.Thm_GlobalTheory_BadShare_ZCalc_conv_zc_of_scalar
import Theorems.Thm_GlobalTheory_BadShare_ZCalc_rk_eq_trace
import Theorems.Thm_PI_CharIdemW_scalar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.ZCalc
variable {G : Type} [Group G] [Fintype G]
namespace GlobalTheory.BadShare.ZCalc
theorem _root_.solution : ∀ (G : Type) [Group G] [Fintype G], ∀ (V : FDRep ℂ G) [CategoryTheory.Simple V], IsProj (zc V.character) ∧ (∀ a : G → ℂ, conv (zc V.character) a = conv a (zc V.character)) ∧ (∀ (W : FDRep ℂ G) [CategoryTheory.Simple W], V.character ≠ W.character → conv (zc V.character) (zc W.character) = 0) ∧ ∀ e : G → ℂ, conv e e = e → conv (zc V.character) e 1 = (Module.finrank ℂ V : ℂ) * (rk V.ρ e : ℂ) / (Fintype.card G : ℂ) := by
  intro G _ _ V hV
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · funext x
    have h := (PI.CharIdemW.scalar G V V hV hV).1 ⟨CategoryTheory.Iso.refl V⟩
    rw [conv_zc_of_scalar _ V 1 (by rw [op_zc, h, one_smul]), one_mul]
  · intro x
    simp only [zc, map_mul, map_div₀, FDRep.char_one, map_natCast]
    rw [character_inv V x⁻¹]
  · intro a
    funext x
    simp only [conv]
    refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x)) _ _ fun y => ?_
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulRight, zc]
    have : V.character ((y⁻¹ * x)⁻¹ * x)⁻¹ = V.character y⁻¹ := by
      rw [← FDRep.char_conj V y⁻¹ x⁻¹]
      congr 1
      group
    rw [this, mul_comm]
  · intro W hW hne
    funext x
    have h := (PI.CharIdemW.scalar G V W hV hW).2 ⟨fun i => hne (FDRep.char_iso i)⟩
    rw [conv_zc_of_scalar _ W 0 (by rw [op_zc, h, zero_smul]), zero_mul]
    rfl
  · intro e he
    rw [rk_eq_trace _ e he, conv, Finset.mul_sum, Finset.sum_div]
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun y => ?_
    simp only [Equiv.inv_apply, zc, mul_one, FDRep.char_one]
    rw [show LinearMap.trace ℂ V (V.ρ y⁻¹) = V.character y⁻¹ from rfl]
    ring
end GlobalTheory.BadShare.ZCalc
