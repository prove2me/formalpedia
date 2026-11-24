-- Prove2me | solution 1 for GlobalTheory.T.fourierEtaleK_eq_integral_partialFourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:09:33.702883+00:00
-- url     : https://prove2.me/submissions/b8ea0d7c-212a-4a5d-94a8-5fb9404a3b34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierEtaleKEqIntegralPartialFourier
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnifConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierEtaleKEqIntegralPartialFourierStatement
import Theorems.Thm_GlobalTheory_FourKFub_fourK_eq_fourB_tilde


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → ∀ b c : A.K, A.fourK μK ψ φ' (b, c) = fourB μK (A.kerK ψ) (fun c' => A.tilde μK ψ φ' c' c) b := by
  first | exact @GlobalTheory.FourKFub.fourK_eq_fourB_tilde | exact GlobalTheory.FourKFub.fourK_eq_fourB_tilde | (intros; apply GlobalTheory.FourKFub.fourK_eq_fourB_tilde <;> assumption)
end _root_.GlobalTheory.T
