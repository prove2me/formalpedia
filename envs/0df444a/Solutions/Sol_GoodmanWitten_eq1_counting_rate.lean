-- Prove2me | solution 1 for GoodmanWitten.eq1_counting_rate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:50:21.434623+00:00
-- url     : https://prove2.me/submissions/afb6dcf3-4c35-461e-847a-62d7de2f8071

import Mathlib
import Definitions.Def_GoodmanWitten_basic
open GoodmanWitten

theorem solution : ∃ C : ℝ, |C / 5.8 - 1| ≤ 0.05 ∧
    ∀ A σ ρ v m : ℝ, 0 < A → 0 < m →
      eventRatePerKgDay A σ ρ v m =
        C * (reducedCrossSection A σ m / 1e-38) * (ρ / 1e-24) * (v / 2e7) := by
  refine ⟨6.0e26 * secondsPerDay * 1e-38 * 1e-24 * 2e7 / gramsPerGeV, ?_, ?_⟩
  · unfold secondsPerDay gramsPerGeV
    rw [abs_le]; constructor <;> norm_num
  · intro A σ ρ v m hA hm
    unfold eventRatePerKgDay reducedCrossSection targetNucleiPerKg
    have : gramsPerGeV ≠ 0 := by unfold gramsPerGeV; norm_num
    field_simp
