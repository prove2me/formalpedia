-- Prove2me | solution 1 for GlobalTheory.T.partialFourierHermitianBlock_isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:07:20.088696+00:00
-- url     : https://prove2.me/submissions/cc92e056-1f31-4c94-99bf-c9198a07b143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockIsLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockIsLocallyConstantStatement
import Theorems.Thm_GlobalTheory_fourU_isLocallyConstant


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f → (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → IsLocallyConstant (fourU M ψ f) := by
  first | exact @GlobalTheory.fourU_isLocallyConstant | exact GlobalTheory.fourU_isLocallyConstant | (intros; apply GlobalTheory.fourU_isLocallyConstant <;> assumption)
end _root_.GlobalTheory.T
