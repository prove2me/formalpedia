-- Prove2me | solution 1 for GlobalTheory.HL.invVol_eq_div_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:11:06.971569+00:00
-- url     : https://prove2.me/submissions/74952e27-9981-4937-901c-eb39645ac5c9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL
namespace _root_.GlobalTheory.HL
theorem _root_.solution {G : Type*} [Group G] {D A B : Subgroup G}
    (hA : D ≤ A) (hB : D ≤ B) (h : D.relIndex A ≠ 0) :
    _root_.GlobalTheory.HL.invVol A B = (D.relIndex A : ℝ) / (D.relIndex B : ℝ) := by
  unfold _root_.GlobalTheory.HL.invVol
  have hDC : D ≤ A ⊓ B := le_inf hA hB
  have eA := Subgroup.relIndex_mul_relIndex D (A ⊓ B) A hDC inf_le_left
  have eB := Subgroup.relIndex_mul_relIndex D (A ⊓ B) B hDC inf_le_right
  rw [Subgroup.inf_relIndex_left] at eA
  rw [Subgroup.inf_relIndex_right] at eB
  have ha : D.relIndex (A ⊓ B) ≠ 0 := by
    intro h0
    apply h
    rw [← eA, h0, zero_mul]
  rw [← eA, ← eB, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr ha)]
end _root_.GlobalTheory.HL
end GlobalTheory.HL
