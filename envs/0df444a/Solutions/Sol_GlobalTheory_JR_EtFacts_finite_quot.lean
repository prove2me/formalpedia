-- Prove2me | solution 1 for GlobalTheory.JR.EtFacts.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:14:12.071769+00:00
-- url     : https://prove2.me/submissions/4f25613b-be85-439a-91f7-ff0f91ebf319

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitsQuotSqFiniteEtaleHermitianPairStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddHaarProperSubmoduleEqZeroModuleTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOKStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactFiniteEtaleHermitianPairOKStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsOpenFiniteEtaleHermitianPairOKStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFacts
import Theorems.Thm_GlobalTheory_JR_EtFacts_sq_le_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtFacts
namespace GlobalTheory.JR.EtFacts
theorem _root_.solution [Unram F E] (A : Et F E) (hsq : Finite (A.Kˣ ⧸ (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range)) :
    Finite (A.Kˣ ⧸ (EtMeas.normU A).range) := by
  have : (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have := Subgroup.finiteIndex_of_le (sq_le_range A)
  exact Subgroup.finite_quotient_of_finiteIndex
end GlobalTheory.JR.EtFacts
