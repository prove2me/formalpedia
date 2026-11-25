-- Prove2me | solution 1 for GlobalTheory.T.partialFourier_etaleKProd_locallyConstantCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:50:40.69617+00:00
-- url     : https://prove2.me/submissions/5a7bbdc4-0d9d-4117-9e82-d0935c800dd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierEtaleKProdLocallyConstantCompactSu
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnifConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierEtaleKProdLocallyConstantCompactSuStatement
import Theorems.Thm_GlobalTheory_JR_EtFacts_main
import Theorems.Thm_GlobalTheory_JR_TildeTest_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (fun p : A.K × A.K => A.tilde μK ψ φ' p.1 p.2) := by
  first | exact @GlobalTheory.JR.TildeTest.main | exact GlobalTheory.JR.TildeTest.main | (intros; apply GlobalTheory.JR.TildeTest.main <;> assumption)
end _root_.GlobalTheory.T
