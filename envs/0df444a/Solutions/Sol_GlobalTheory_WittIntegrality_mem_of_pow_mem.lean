-- Prove2me | solution 1 for GlobalTheory.WittIntegrality.mem_of_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:02.475818+00:00
-- url     : https://prove2.me/submissions/44405bc2-b3ca-4390-9927-f81e9476b2cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittMatrixCoeffMemOfFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries Pointwise
open GlobalTheory
open GlobalTheory.WittIntegrality
open WittVector
variable {C : Type} [Field C] (A : ValuationSubring C)
namespace GlobalTheory.WittIntegrality
theorem _root_.solution {c : C} {k : ℕ} (hk : 1 ≤ k) (h : c ^ k ∈ A) : c ∈ A := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rcases A.mem_or_inv_mem c with hc | hc
  · exact hc
  · by_cases h0 : c = 0
    · rw [h0]; exact A.zero_mem
    · have e : c = c ^ (m + 1) * c⁻¹ ^ m := by
        rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ h0, one_pow, mul_one]
      rw [e]; exact mul_mem h (pow_mem hc _)
end GlobalTheory.WittIntegrality
