-- Prove2me | solution 1 for GlobalTheory.T.hermitianFrameClasses_total_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:14:13.99375+00:00
-- url     : https://prove2.me/submissions/73d3b03d-b47f-4513-b6e9-47a1d0753339

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameClassesTotalWeightLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameClassesTotalWeightLeStatement
import Theorems.Thm_GlobalTheory_HL_TotalWeight_sumCls_one_le


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∃ d Λ, S.IsTerm d Λ) → (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (3 * (r + 1) ^ 2)) := by
  first | exact @GlobalTheory.HL.TotalWeight.sumCls_one_le | exact GlobalTheory.HL.TotalWeight.sumCls_one_le | (intros; apply GlobalTheory.HL.TotalWeight.sumCls_one_le <;> assumption)
end _root_.GlobalTheory.T
