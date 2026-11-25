-- Prove2me | solution 1 for GlobalTheory.FrameAct.relIndex_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:31:37.349874+00:00
-- url     : https://prove2.me/submissions/97003e0a-2986-4859-8a1e-6104b23d4566

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms

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
open GlobalTheory GlobalTheory.FrameAct
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.FrameAct
theorem _root_.solution (h : S.GLV) (A B : Submodule L.O S.V) :
    (h • A).toAddSubgroup.relIndex (h • B).toAddSubgroup =
      A.toAddSubgroup.relIndex B.toAddSubgroup := by
  have hA : (h • A).toAddSubgroup = A.toAddSubgroup.map (h.toLinearMap.toAddMonoidHom) := by
    ext x; rfl
  have hB : (h • B).toAddSubgroup = B.toAddSubgroup.map (h.toLinearMap.toAddMonoidHom) := by
    ext x; rfl
  rw [hA, hB]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ h.injective
end GlobalTheory.FrameAct
