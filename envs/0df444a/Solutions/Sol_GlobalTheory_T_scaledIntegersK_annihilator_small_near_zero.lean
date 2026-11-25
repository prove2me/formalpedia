-- Prove2me | solution 1 for GlobalTheory.T.scaledIntegersK_annihilator_small_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:50:41.363963+00:00
-- url     : https://prove2.me/submissions/ae852fde-fee9-4685-94d2-e94a835af024

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ScaledIntegersKAnnihilatorSmallNearZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ScaledIntegersKAnnihilatorSmallNearZeroStatement
import Theorems.Thm_GlobalTheory_JR_annihilator_small


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ U ∈ 𝓝 (0 : A.K), ∀ᶠ c in 𝓝[≠] (0 : F), ∀ b : A.K, (∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1) → b ∈ U := by
  first | exact @GlobalTheory.JR.annihilator_small | exact GlobalTheory.JR.annihilator_small | (intros; apply GlobalTheory.JR.annihilator_small <;> assumption)
end _root_.GlobalTheory.T
