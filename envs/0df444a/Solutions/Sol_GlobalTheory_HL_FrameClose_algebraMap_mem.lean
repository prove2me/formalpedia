-- Prove2me | solution 1 for GlobalTheory.HL.FrameClose.algebraMap_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:38.610675+00:00
-- url     : https://prove2.me/submissions/026d7b80-2e6d-4204-91de-55dd5fd42512

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitriangularCloseToOneInverseCloseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingConjInverseAdjointCloseToOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemMaximalCompactOfIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalPairingMatrixInvMulSelfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalFramesJointGramInvMulSelfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsCommonDenominatorForHermitianLatticeDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CloseOnCompletedLatticeOfCloseOnFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntCastIsUnitCompletionAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMatrixCloseGivesLatticeCloseIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameClose
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.FrameClose
theorem _root_.solution (L : LocE F E) {a : F} (ha : a ∈ 𝒪[F]) : algebraMap F E a ∈ L.O := by
  rw [L.O_def]
  exact isIntegral_algebraMap (R := 𝒪[F]) (x := (⟨a, ha⟩ : 𝒪[F]))
end GlobalTheory.HL.FrameClose
