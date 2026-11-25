-- Prove2me | solution 1 for GlobalTheory.Dyadic.exists_shell_down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:34:53.022845+00:00
-- url     : https://prove2.me/submissions/e97b9bcf-4830-44e7-9004-06cb8e990117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LintegralBoundByDyadicSummation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.Dyadic
namespace GlobalTheory.Dyadic
theorem _root_.solution (y T : ℝ) (hy : 0 < y) (hT : y ≤ T) :
    ∃ a : ℕ, T / 2 ^ (a + 1) < y ∧ y ≤ 2 * (T / 2 ^ (a + 1)) := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (x := T / y) (y := (2 : ℝ))
    ((one_le_div hy).2 hT) one_lt_two
  refine ⟨n, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hy] at h2; linarith
  · rw [le_div_iff₀ hy] at h1
    have : 2 * (T / 2 ^ (n + 1)) = T / 2 ^ n := by rw [pow_succ]; field_simp
    rw [this, le_div_iff₀ (by positivity)]; linarith
end GlobalTheory.Dyadic
