-- Prove2me | solution 1 for GlobalTheory.HL.GoodSub.cont_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:29:10.834208+00:00
-- url     : https://prove2.me/submissions/d29ce93b-6e48-40dc-a33c-ea8c039d0079

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonneg
import Theorems.Thm_GlobalTheory_HL_GoodSub_count_eq

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
theorem _root_.solution {W : Type} [AddCommGroup W] {W0 A : AddSubgroup W} {S : Set W}
    (hA : GoodSub W0 A S) :
    cont W0 S = (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A := by
  have h : IsCO W0 S := ⟨A, hA⟩
  unfold cont
  rw [dif_pos h]
  exact GoodSub.count_eq h.choose_spec hA
end GoodSub
end GlobalTheory.HL
