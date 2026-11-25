-- Prove2me | solution 1 for GlobalTheory.T.exists_large_vonMangoldtLogPowerSeries_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:26:46.977256+00:00
-- url     : https://prove2.me/submissions/6697866a-c47d-46c7-a1f1-215913c4448d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLargeVonMangoldtLogPowerSeriesNearZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLargeVonMangoldtLogPowerSeriesNearZeroStatement
import Theorems.Thm_GlobalTheory_NearZeroDeriv_exists_large_derSeries


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∃ A C r₀ : ℝ, 1 ≤ A ∧ 0 < C ∧ 0 < r₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (τ r L : ℝ) (K : ℕ) (ρ : ℂ), (χ ≠ 1 ∨ 2 ≤ |τ|) → Real.log (q * (|τ| + 2)) ≤ L → 1 / L ≤ r → r ≤ r₀ → C * r * L ≤ K → LFunction χ ρ = 0 → ‖ρ - (1 + τ * I)‖ ≤ r → ∃ k : ℕ, K ≤ k ∧ k ≤ 2 * K ∧ 1 / (A * r) ^ (k + 1) ≤ ‖derSeries (fun n : ℕ => χ (n : ZMod q)) k ((1 + r : ℝ) + τ * I)‖ := by
  first | exact @GlobalTheory.NearZeroDeriv.exists_large_derSeries | exact GlobalTheory.NearZeroDeriv.exists_large_derSeries | (intros; apply GlobalTheory.NearZeroDeriv.exists_large_derSeries <;> assumption)
end _root_.GlobalTheory.T
