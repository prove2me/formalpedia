-- Prove2me | solution 1 for GlobalTheory.ThickLevel.finite_image_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:57.041149+00:00
-- url     : https://prove2.me/submissions/de085dba-6288-438f-b330-3ac6fd2222c8

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
theorem _root_.solution {W : Type} [AddCommGroup W] (B C : AddSubgroup W) (h : C.relIndex B ≠ 0)
    (T : Set W) (hT : ((QuotientAddGroup.mk : W → W ⧸ B) '' T).Finite) :
    ((QuotientAddGroup.mk : W → W ⧸ C) '' T).Finite := by
  have : (C.addSubgroupOf B).FiniteIndex := ⟨h⟩
  let f : B ⧸ C.addSubgroupOf B →+ W ⧸ C := QuotientAddGroup.map _ _ B.subtype le_rfl
  have hfin : (Set.range f).Finite := Set.finite_range _
  refine (hT.biUnion (t := fun q => (fun z => (QuotientAddGroup.mk q.out : W ⧸ C) + z) '' Set.range f)
    (fun q _ => hfin.image _)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine Set.mem_biUnion (x := (QuotientAddGroup.mk x : W ⧸ B)) ⟨x, hx, rfl⟩ ?_
  have hb : -(QuotientAddGroup.mk x : W ⧸ B).out + x ∈ B := by
    rw [← QuotientAddGroup.eq]; simp
  refine ⟨_, ⟨QuotientAddGroup.mk ⟨_, hb⟩, rfl⟩, ?_⟩
  change (QuotientAddGroup.mk _ : W ⧸ C) + QuotientAddGroup.mk (-(QuotientAddGroup.mk x : W ⧸ B).out + x) = _
  rw [← QuotientAddGroup.mk_add, add_neg_cancel_left]
end GlobalTheory.ThickLevel
