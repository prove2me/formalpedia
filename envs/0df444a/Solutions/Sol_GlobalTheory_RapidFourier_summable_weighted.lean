-- Prove2me | solution 1 for GlobalTheory.RapidFourier.summable_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:26:06.865994+00:00
-- url     : https://prove2.me/submissions/44470d89-a227-4db6-8f4d-d4ec387c6547

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Theorems.Thm_GlobalTheory_RapidFourier_summable_inv_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.RapidFourier
namespace GlobalTheory.RapidFourier
theorem _root_.solution {n : ℕ} {c : (Fin n → ℤ) → ℂ}
    (hc : ∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C) (m : ℕ) :
    Summable fun ν => ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m := by
  obtain ⟨C, hC⟩ := hc (m + 2 * n)
  refine Summable.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_)
    ((summable_inv_pow n).mul_left C)
  have hpos : 0 < (1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_assoc, ← pow_add]
  exact hC ν
end GlobalTheory.RapidFourier
