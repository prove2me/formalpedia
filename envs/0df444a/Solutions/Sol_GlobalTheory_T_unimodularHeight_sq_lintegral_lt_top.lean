-- Prove2me | solution 1 for GlobalTheory.T.unimodularHeight_sq_lintegral_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:55:44.100801+00:00
-- url     : https://prove2.me/submissions/4ef2f07d-a6bf-4cce-bab0-351c27893ed1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHeightSqLintegralLtTop
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHeightSqLintegralLtTopStatement
import Theorems.Thm_GlobalTheory_JR_HeightSquareIntegrable_height_sq_lintegral_lt_top


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.K), μ.IsAddHaarMeasure → ∫⁻ z, (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ < ⊤ := by
  first | exact @GlobalTheory.JR.HeightSquareIntegrable.height_sq_lintegral_lt_top | exact GlobalTheory.JR.HeightSquareIntegrable.height_sq_lintegral_lt_top | (intros; apply GlobalTheory.JR.HeightSquareIntegrable.height_sq_lintegral_lt_top <;> assumption)
end _root_.GlobalTheory.T
