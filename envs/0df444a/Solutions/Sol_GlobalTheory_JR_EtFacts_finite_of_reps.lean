-- Prove2me | solution 1 for GlobalTheory.JR.EtFacts.finite_of_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:58:38.346814+00:00
-- url     : https://prove2.me/submissions/1843f7b0-8eee-474f-9818-664792fdfa5d

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
import Theorems.Thm_GlobalTheory_JR_EtFacts_key_rel

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
theorem _root_.solution [Unram F E] (A : Et F E) (hf : Finite (A.Kˣ ⧸ (EtMeas.normU A).range)) (S : Set A.Kˣ)
    (hS : A.IsReps S) : S.Finite := by
  have hinj : Function.Injective (fun x : S => (QuotientGroup.mk (x : A.Kˣ) : A.Kˣ ⧸ (EtMeas.normU A).range)) := by
    rintro ⟨x, hx⟩ ⟨x', hx'⟩ h
    obtain ⟨z, -, hz⟩ := hS x'
    have e1 := hz x ⟨hx, (key_rel A _ _).2 h⟩
    have e2 := hz x' ⟨hx', (key_rel A _ _).2 rfl⟩
    exact Subtype.ext (e1.trans e2.symm)
  exact Set.finite_coe_iff.1 (Finite.of_injective _ hinj)
end GlobalTheory.JR.EtFacts
