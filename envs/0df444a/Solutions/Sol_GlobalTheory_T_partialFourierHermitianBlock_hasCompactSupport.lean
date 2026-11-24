-- Prove2me | solution 1 for GlobalTheory.T.partialFourierHermitianBlock_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:07:18.848196+00:00
-- url     : https://prove2.me/submissions/e421f9a6-6e4d-4ad3-b8e9-fe551a8b2403

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockHasCompactSupport
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockHasCompactSupportStatement
import Theorems.Thm_GlobalTheory_fourU_hasCompactSupport


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f → (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → HasCompactSupport (fourU M ψ f) := by
  first | exact @GlobalTheory.fourU_hasCompactSupport | exact GlobalTheory.fourU_hasCompactSupport | (intros; apply GlobalTheory.fourU_hasCompactSupport <;> assumption)
end _root_.GlobalTheory.T
