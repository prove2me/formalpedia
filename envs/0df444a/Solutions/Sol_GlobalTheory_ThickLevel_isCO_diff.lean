-- Prove2me | solution 1 for GlobalTheory.ThickLevel.isCO_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:06:21.632334+00:00
-- url     : https://prove2.me/submissions/2c890479-89b3-4c77-9b38-1b9ed290bf09

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentBiUnionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalisedContentThickenedSetIndependentOfLevel
import Theorems.Thm_GlobalTheory_ThickLevel_finite_image_of_le
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.ThickLevel
namespace GlobalTheory.ThickLevel
theorem _root_.solution {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {S T : Set W}
    (hS : IsCO W0 S) (hT : IsCO W0 T) : IsCO W0 (T \ S) := by
  obtain ⟨A, hA1, hA2, hA3, -⟩ := hS
  obtain ⟨B, hB1, hB2, hB3, hB4⟩ := hT
  refine ⟨A ⊓ B, AddSubgroup.relIndex_inf_ne_zero hA1 hB1, ?_, ?_, ?_⟩
  · intro h
    exact hA2 (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  · rintro x ⟨hx, hx'⟩ a ⟨ha, hb⟩
    refine ⟨hB3 x hx a hb, fun h => hx' ?_⟩
    simpa using hA3 _ h (-a) (A.neg_mem ha)
  · refine (finite_image_of_le B (A ⊓ B) ?_ T hB4).subset (Set.image_mono Set.diff_subset)
    rw [AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_ne_zero_trans hA1 hB2
end GlobalTheory.ThickLevel
