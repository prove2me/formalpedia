-- Prove2me | solution 1 for GlobalTheory.T.haar_lintegral_mul_right_le_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:35.434983+00:00
-- url     : https://prove2.me/submissions/1ddfede5-3acc-41f6-89d4-add8c533d961

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarLintegralMulRightLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarLintegralMulRightLeStatement
import Theorems.Thm_GlobalTheory_haar_lintegral_mul_right_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ y ∈ K, ∀ φ : H → ENNReal, Measurable φ → ∫⁻ x, φ (x * y) ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by
  first | exact @GlobalTheory.haar_lintegral_mul_right_le | exact GlobalTheory.haar_lintegral_mul_right_le | (intros; apply GlobalTheory.haar_lintegral_mul_right_le <;> assumption)
end _root_.GlobalTheory.T
