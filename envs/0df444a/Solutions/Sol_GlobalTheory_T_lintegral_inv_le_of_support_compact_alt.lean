-- Prove2me | solution 1 for GlobalTheory.T.lintegral_inv_le_of_support_compact_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:25:48.665664+00:00
-- url     : https://prove2.me/submissions/187be043-1352-46e0-8a21-e579f5b35287

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralInvLeOfSupportCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralInvLeOfSupportCompactStatement
import Theorems.Thm_GlobalTheory_lintegral_inv_le_of_support_compact


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
theorem _root_.solution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ φ : H → ENNReal, Measurable φ → (∀ x ∉ K, φ x = 0) → ∫⁻ x, φ x⁻¹ ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by
  first | exact @GlobalTheory.lintegral_inv_le_of_support_compact | exact GlobalTheory.lintegral_inv_le_of_support_compact | (intros; apply GlobalTheory.lintegral_inv_le_of_support_compact <;> assumption)
end _root_.GlobalTheory.T
