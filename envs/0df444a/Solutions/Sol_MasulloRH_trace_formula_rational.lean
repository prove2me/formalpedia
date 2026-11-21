-- Prove2me | solution 1 for MasulloRH.trace_formula_rational
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:17:46.746186+00:00
-- url     : https://prove2.me/submissions/1e940273-2030-4373-b8f9-25247b2f1e74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_realTraceIntegrand_integrable
import Theorems.Thm_MasulloRH_primePowerTraceTerm_finite_support
import Theorems.Thm_MasulloRH_spectral_trace_hasSum
import Mathlib.Tactic.Abel

open MasulloRH MeasureTheory Set

theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧ Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  have h := spectral_trace_hasSum α hα φ hφ
  refine ⟨realTraceIntegrand_integrable φ hφ,
    summable_of_hasFiniteSupport (primePowerTraceTerm_finite_support φ hφ), h.summable, ?_⟩
  rw [h.tsum_eq]
  abel
