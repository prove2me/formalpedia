-- Prove2me | solution 1 for GlobalTheory.HL.CoordGood.adjugate_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:02:04.062858+00:00
-- url     : https://prove2.me/submissions/e5086a8b-5bff-4b75-91c6-01d89d90419c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEquivOfRetractions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsGluingHomomorphismDefectGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralOfMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HmUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCoordinateLatticeIsTermTrivialWitnesses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordGood
open GlobalTheory.HL.Model GlobalTheory.HL.Inhab
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.CoordGood
theorem _root_.solution (L : LocE F E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (h : IsIntM L A) :
    IsIntM L A.adjugate := by
  let B : Matrix (Fin n) (Fin n) L.O := fun i j => ⟨A i j, h i j⟩
  have hB : A = L.O.subtype.mapMatrix B := by ext i j; rfl
  rw [hB, ← RingHom.map_adjugate]
  intro i j
  exact (B.adjugate i j).2
end GlobalTheory.HL.CoordGood
