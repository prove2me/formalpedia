-- Prove2me | solution 1 for GlobalTheory.PrimeSquareSum.summable_absNorm_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:40:32.256452+00:00
-- url     : https://prove2.me/submissions/e85fa641-c75a-4016-88d0-852933a93311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableAbsNormInvSq
import Theorems.Thm_GlobalTheory_PrimeSquareSum_sum_absNorm_inv_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.PrimeSquareSum
namespace GlobalTheory.PrimeSquareSum
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K], Summable (fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹) ∧ ∑' w : HeightOneSpectrum (𝓞 K), (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) := by
  intro K _ _
  have hnn : 0 ≤ fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ :=
    fun w => by positivity
  exact ⟨summable_of_sum_le hnn (sum_absNorm_inv_sq_le K),
    tsum_le_of_sum_le' (by positivity) (sum_absNorm_inv_sq_le K)⟩
end GlobalTheory.PrimeSquareSum
