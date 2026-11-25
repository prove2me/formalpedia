-- Prove2me | solution 1 for GlobalTheory.ThickOrbit.relIndex_ne_zero_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:56:44.21061+00:00
-- url     : https://prove2.me/submissions/3e35827a-fdec-4ae4-8015-0d0d7444204f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryNearIdentityCloseTuplesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryTupleMatrixRightMulNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ThickOrbitSelfDualUnramifiedLattice
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
open GlobalTheory GlobalTheory.ThickOrbit
namespace GlobalTheory.ThickOrbit
theorem _root_.solution {W : Type} [AddCommGroup W] (A B : AddSubgroup W)
    (h : ((QuotientAddGroup.mk : W → W ⧸ A) '' (B : Set W)).Finite) : A.relIndex B ≠ 0 := by
  have : Finite (B ⧸ A.addSubgroupOf B) := by
    have := h.to_subtype
    let f : B ⧸ A.addSubgroupOf B → ((QuotientAddGroup.mk : W → W ⧸ A) '' (B : Set W)) := fun q =>
      ⟨QuotientAddGroup.mk (q.out : W), q.out, q.out.2, rfl⟩
    refine Finite.of_injective f fun a b hab => ?_
    have h1 : (QuotientAddGroup.mk (a.out : W) : W ⧸ A) = QuotientAddGroup.mk (b.out : W) :=
      congrArg Subtype.val hab
    rw [QuotientAddGroup.eq] at h1
    rw [← a.out_eq', ← b.out_eq', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simpa using h1
  exact AddSubgroup.index_ne_zero_of_finite
end GlobalTheory.ThickOrbit
