-- Prove2me | solution 1 for GlobalTheory.JR.EtFacts.sq_le_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:58:42.951836+00:00
-- url     : https://prove2.me/submissions/8795d2f3-05b1-4434-85b1-79e677770586

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
import Theorems.Thm_GlobalTheory_JR_EtMeas_normU_val
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure


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
theorem _root_.solution [Unram F E] (A : Et F E) :
    (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range ≤ (EtMeas.normU A).range := by
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  rintro _ ⟨k, rfl⟩
  refine ⟨Units.map (algebraMap A.K A.L).toMonoidHom k, Units.ext (hinj ?_)⟩
  rw [EtMeas.normU_val, hN]
  simp [A.star_K, sq]
end GlobalTheory.JR.EtFacts
