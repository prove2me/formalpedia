-- Prove2me | solution 1 for GlobalTheory.HL.MoveTotal.norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:42:03.791743+00:00
-- url     : https://prove2.me/submissions/f068ee52-967a-4e01-b5f3-8cda6e779c45

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMoveCharacterNeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralProdFubiniStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexIntegrableShareTopLevelVectorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMoveScalarFibreMeasureOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermIntegralNearOneBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovesTotalMeasureEstimates
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_indexMeasureIntegral_linear_positive_norm_bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveTotal
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {W W₁ W₂ W₃ : Type} [AddCommGroup W] [AddCommGroup W₁] [AddCommGroup W₂] [AddCommGroup W₃]
namespace GlobalTheory.HL.MoveTotal
theorem _root_.solution (A : AddSubgroup W) (P : W → Prop) (h : Nice A (ind P)) (φ : W → ℂ)
    (hφ : Nice A (fun w => ind P w * φ w)) (m : ℝ) (hm : ∀ w, P w → ‖φ w‖ ≤ m) :
    ‖cint A (fun w => ind P w * φ w)‖ ≤ m * (cint A (ind P)).re := by
  obtain ⟨e1, e2⟩ := (GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound A).2.1 (m : ℂ) _ h
  have := ((GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound A).1 _ _ hφ e1).2.2 fun w => by
    by_cases hw : P w
    · simpa [ind, hw] using hm w hw
    · simp [ind, hw]
  rw [e2] at this
  simpa using this
end GlobalTheory.HL.MoveTotal
