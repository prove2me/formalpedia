-- Prove2me | solution 1 for GlobalTheory.T.jHyp_mem_induced_fourier_weyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:14.525088+00:00
-- url     : https://prove2.me/submissions/24455bb4-5bd5-4855-980e-12c7d879a4a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JHypMemInducedFourierWeyl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JHypMemInducedFourierWeylStatement
import Theorems.Thm_GlobalTheory_EtaChar_main
import Theorems.Thm_GlobalTheory_JR_EtFacts_main
import Theorems.Thm_GlobalTheory_JR_HypJ_main
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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ', IsTest φ' → A.InI (A.jHyp μK ψ φ') ∧ ∀ h, A.jHyp μK ψ (A.fourK μK ψ φ') h = A.jHyp μK ψ φ' (h * wS A.K) := by
  first | exact @GlobalTheory.JR.HypJ.main | exact GlobalTheory.JR.HypJ.main | (intros; apply GlobalTheory.JR.HypJ.main <;> assumption)
end _root_.GlobalTheory.T
