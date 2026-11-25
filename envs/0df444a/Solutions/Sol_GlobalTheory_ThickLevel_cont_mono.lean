-- Prove2me | solution 1 for GlobalTheory.ThickLevel.cont_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:33:50.222585+00:00
-- url     : https://prove2.me/submissions/cf6fd19f-3ae0-4ac1-804a-30f57216cbaf

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
import Theorems.Thm_GlobalTheory_ThickLevel_isCO_diff
import Theorems.Thm_GlobalTheory_ThickLevel_cont_nonneg
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_commensurableCosetUnionContent_biUnion
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
    (hS : IsCO W0 S) (hT : IsCO W0 T) (h : S ⊆ T) : cont W0 S ≤ cont W0 T := by
  have h1 := (GlobalTheory.T.commensurableCosetUnionContent_biUnion W0 (Finset.univ : Finset Bool) (fun b => if b then S else T \ S)
    (by rintro (_ | _) _
        · simpa using isCO_diff W0 hS hT
        · simpa using hS)).2
    (by rintro (_ | _) _ (_ | _) _ hne
        · exact absurd rfl hne
        · simpa using Set.disjoint_sdiff_left
        · simpa using Set.disjoint_sdiff_right
        · exact absurd rfl hne)
  have h2 : (⋃ i ∈ (Finset.univ : Finset Bool), if i then S else T \ S) = T := by
    ext x
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, Bool.exists_bool]
    simp only [Bool.false_eq_true, if_false, if_true, Set.mem_diff]
    have := @h x
    tauto
  rw [h2] at h1
  simp at h1
  have := cont_nonneg W0 (T \ S)
  linarith
end GlobalTheory.ThickLevel
