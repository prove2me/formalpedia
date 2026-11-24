-- Prove2me | solution 1 for GlobalTheory.irrChar_one_mul_finsum_conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:06:02.420731+00:00
-- url     : https://prove2.me/submissions/9998d068-5905-49d1-88e2-703ea075cf57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrrCharOneMulFinsumConjMul
import Theorems.Thm_GlobalTheory_character_one_mul_sum_conj_mul

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
namespace GlobalTheory
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), IsIrrChar ℂ ℂ χ → ∀ x y : G, χ 1 * ∑ᶠ h : G, χ (h * x * h⁻¹ * y) = (Nat.card G : ℂ) * (χ x * χ y) := by
  intro G _ _ χ hχ x y
  let := Fintype.ofFinite G
  obtain ⟨n, ρ, hρ, h⟩ := hχ
  have hh : χ = ρ.character := by
    funext g
    simpa using h g
  subst hh
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  exact character_one_mul_sum_conj_mul ρ x y
end GlobalTheory
