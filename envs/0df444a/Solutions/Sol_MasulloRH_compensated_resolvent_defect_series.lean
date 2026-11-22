-- Prove2me | solution 1 for MasulloRH.compensated_resolvent_defect_series
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T00:32:40.680796+00:00
-- url     : https://prove2.me/submissions/a71554ad-f99a-4f97-ba1e-db8317cacae7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_compensated_resolvent_defect_low_high_split

open MasulloRH

theorem solution
    (α : ℝ) (hα : 0 < α) (hsmall : α < 1 / 2)
    (hkernel :
      ∀ (β γ T : ℝ), 0 ≤ β → β ≤ 1 → 36 ≤ γ ^ 2 →
        let a := 3 - β
        let b := 5 / 2 - β
        let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
        let k := a / (a ^ 2 + (T - γ) ^ 2) - b / (b ^ 2 + γ ^ 2) + 8 * c0
        0 < k ∧ a / (a ^ 2 + (T - γ) ^ 2) ≤ k) :
    ∃ f : ZetaZerosInTraceStrip (1 / 2) → ℝ,
      (∀ ρ, 0 ≤ f ρ) ∧ Summable f ∧
        (regularizedTraceRHS α 3).re - (regularizedTraceRHS (1 / 2) 3).re = ∑' ρ, f ρ := by
  rcases compensated_resolvent_defect_low_high_split α hα hsmall hkernel with
    ⟨F, hF, hcover, fLow, fHigh, hLow, hHigh, hLowSupp, hHighSupp,
      hSumLow, hSumHigh, hEq⟩
  let f : ZetaZerosInTraceStrip (1 / 2) → ℝ := fun ρ => fLow ρ + fHigh ρ
  have hf_nonneg : ∀ ρ, 0 ≤ f ρ := by
    intro ρ
    dsimp [f]
    exact add_nonneg (hLow ρ) (hHigh ρ)
  have hf_sum : Summable f := by
    dsimp [f]
    exact hSumLow.add hSumHigh
  refine ⟨f, hf_nonneg, hf_sum, ?_⟩
  rw [hEq]
  simpa [f] using (hSumLow.tsum_add hSumHigh).symm
