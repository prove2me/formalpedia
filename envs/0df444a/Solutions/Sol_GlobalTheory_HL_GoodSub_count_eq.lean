-- Prove2me | solution 1 for GlobalTheory.HL.GoodSub.count_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:20:14.065798+00:00
-- url     : https://prove2.me/submissions/5e2eace5-f476-4824-a03f-59de1f296785

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonneg
import Theorems.Thm_GlobalTheory_HL_GoodSub_count_eq_of_le

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
namespace GlobalTheory.HL
namespace GoodSub
theorem _root_.solution {W : Type} [AddCommGroup W] {W0 A B : AddSubgroup W} {S : Set W}
    (hA : GoodSub W0 A S) (hB : GoodSub W0 B S) :
    (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A =
      (((QuotientAddGroup.mk : W → W ⧸ B) '' S).ncard : ℝ) * relVol W0 B := by
  have i1 : (A ⊓ B).relIndex A ≠ 0 := by
    rw [AddSubgroup.inf_relIndex_left]
    exact AddSubgroup.relIndex_ne_zero_trans hB.1 hA.2.1
  have i2 : (A ⊓ B).relIndex B ≠ 0 := by
    rw [AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_ne_zero_trans hA.1 hB.2.1
  rw [hA.count_eq_of_le inf_le_left i1, hB.count_eq_of_le inf_le_right i2]
end GoodSub
end GlobalTheory.HL
