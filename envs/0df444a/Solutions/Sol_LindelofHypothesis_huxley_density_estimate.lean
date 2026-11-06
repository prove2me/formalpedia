-- Prove2me | solution 1 for LindelofHypothesis.huxley_density_estimate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:33:23.681287+00:00
-- url     : https://prove2.me/submissions/6d10c5fd-7308-482a-a7a8-41eb6cad9893
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GuthMaynard_huxley_density_estimate_uniform

open Filter Topology Asymptotics
open scoped ENNReal

namespace GuthMaynard.CitedZeros

/-! ## Monotonicity of `N(σ, T)` -/

/-! ## Goal 1 -/

lemma log_pow_le_rpow {ε : ℝ} (hε : 0 < ε) : ∀ᶠ T in atTop, Real.log T ^ 44 ≤ T ^ ε := by
  have h := (isLittleO_log_rpow_rpow_atTop (44 : ℝ) hε).bound one_pos
  filter_upwards [h, eventually_ge_atTop 1] with T hT h1
  have hl : 0 ≤ Real.log T := Real.log_nonneg h1
  have hT0 : (0 : ℝ) < T := by linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul] at hT
  have : Real.log T ^ (44 : ℝ) = Real.log T ^ (44 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  rw [← this]; exact hT

theorem huxley_dev (σ : ℝ) (hσ₀ : 3 / 4 ≤ σ) (hσ₁ : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ T in atTop,
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (3 / (3 * σ - 1) * (1 - σ) + ε)) := by
  obtain ⟨C, hC⟩ := GuthMaynard.huxley_density_estimate_uniform
  refine ⟨max C 0, ?_⟩
  filter_upwards [log_pow_le_rpow hε, eventually_ge_atTop 2] with T hlog hT
  refine (hC T hT σ hσ₀ hσ₁).trans (ENNReal.ofReal_le_ofReal ?_)
  have hT0 : 0 < T := by linarith
  have hexp : 3 * (1 - σ) / (3 * σ - 1) = 3 / (3 * σ - 1) * (1 - σ) := by ring
  rw [hexp, Real.rpow_add hT0]
  have h1 : 0 ≤ T ^ (3 / (3 * σ - 1) * (1 - σ)) := by positivity
  have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ Real.log T ^ 44 := by positivity
  have hm : 0 ≤ max C 0 := le_max_right _ _
  calc C * T ^ (3 / (3 * σ - 1) * (1 - σ)) * Real.log T ^ 44
      ≤ max C 0 * T ^ (3 / (3 * σ - 1) * (1 - σ)) * Real.log T ^ 44 := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * (T ^ (3 / (3 * σ - 1) * (1 - σ)) * T ^ ε) := by
        rw [mul_assoc]; gcongr

/-! ## Goal 2 -/

end GuthMaynard.CitedZeros

open LindelofHypothesis in
theorem solution (σ : ℝ) (hσ₀ : 3 / 4 ≤ σ) (hσ₁ : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ T in atTop,
      (zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal (C * T ^ (3 / (3 * σ - 1) * (1 - σ) + ε)) :=
  GuthMaynard.CitedZeros.huxley_dev σ hσ₀ hσ₁ ε hε
