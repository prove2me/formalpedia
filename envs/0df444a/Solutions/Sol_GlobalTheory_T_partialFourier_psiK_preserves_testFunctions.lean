-- Prove2me | solution 1 for GlobalTheory.T.partialFourier_psiK_preserves_testFunctions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:48.558891+00:00
-- url     : https://prove2.me/submissions/0c0ebdd1-5904-45da-b470-1691b367b1cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierPsiKPreservesTestFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierPsiKPreservesTestFunctionsStatement
import Theorems.Thm_GlobalTheory_JR_Hyp_pt_isTest


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ) := by
  first | exact @GlobalTheory.JR.Hyp.pt_isTest | exact GlobalTheory.JR.Hyp.pt_isTest | (intros; apply GlobalTheory.JR.Hyp.pt_isTest <;> assumption)
end _root_.GlobalTheory.T
