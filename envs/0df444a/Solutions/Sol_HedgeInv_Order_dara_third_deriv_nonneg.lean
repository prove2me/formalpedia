-- Prove2me | solution 1 for HedgeInv.Order.dara_third_deriv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:05:45.481177+00:00
-- url     : https://prove2.me/submissions/a631cd69-ca74-4ac7-b633-208bcf1cba4b

import Mathlib
import Definitions.Def_MDPFinance_FinancialMarkets_Utility

theorem solution (u : ℝ → ℝ) (hu : ContDiff ℝ 3 u)
    (hu1 : ∀ w, 0 < deriv u w) (hu2 : ∀ w, deriv (deriv u) w < 0)
    (hDARA : Antitone (MDPFinance.FinancialMarkets.arrowPrattCoefficient u)) :
    ∀ w, 0 ≤ deriv (deriv (deriv u)) w := by
  intro w
  obtain ⟨hd1, -, hc2⟩ := contDiff_succ_iff_deriv.mp (hu.of_le (by norm_num) : ContDiff ℝ (2+1) u)
  obtain ⟨hd2, -, hc1⟩ := contDiff_succ_iff_deriv.mp (hc2.of_le (by norm_num) : ContDiff ℝ (1+1) (deriv u))
  obtain ⟨hd3, -, -⟩ := contDiff_succ_iff_deriv.mp (hc1.of_le (by norm_num) : ContDiff ℝ (0+1) (deriv (deriv u)))
  have hD : HasDerivAt (MDPFinance.FinancialMarkets.arrowPrattCoefficient u)
      ((-(deriv (deriv (deriv u)) w) * deriv u w - (-(deriv (deriv u) w)) * deriv (deriv u) w)
        / (deriv u w) ^ 2) w := by
    have h1 := ((hd3 w).hasDerivAt).neg
    have h2 := (hd2 w).hasDerivAt
    have := h1.div h2 (hu1 w).ne'
    exact this
  have hle := hDARA.deriv_nonpos (x := w)
  rw [hD.deriv] at hle
  have hp := hu1 w
  have hsq : 0 < (deriv u w) ^ 2 := by positivity
  have hnum : -(deriv (deriv (deriv u)) w) * deriv u w - (-(deriv (deriv u) w)) * deriv (deriv u) w ≤ 0 := by
    by_contra hc
    push_neg at hc
    have := div_pos hc hsq
    linarith
  by_contra hc
  push_neg at hc
  nlinarith [sq_nonneg (deriv (deriv u) w), mul_pos (neg_pos.mpr hc) hp]
