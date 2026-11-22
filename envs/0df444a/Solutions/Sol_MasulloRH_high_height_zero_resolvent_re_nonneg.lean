-- Prove2me | solution 1 for MasulloRH.high_height_zero_resolvent_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T08:16:16.252538+00:00
-- url     : https://prove2.me/submissions/0ef1e513-4550-4606-909a-8beb4a71d5e0

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_compensated_resolvent_baseline_pos

set_option autoImplicit false
open MasulloRH

theorem solution (ρ : ZetaZerosInTraceStrip (1 / 2))
    (hheight : 36 ≤ ρ.val.im ^ 2) :
    0 ≤ (zeroResolventTerm (1 / 2) (3 : ℂ) ρ).re := by
  let β : ℝ := ρ.val.re
  let γ : ℝ := ρ.val.im
  have hβ0 : 0 ≤ β := le_of_lt ρ.property.2.1
  have hβ1 : β ≤ 1 := le_of_lt ρ.property.2.2.1
  have hc0 : 0 <
      (3 - β) / ((3 - β) ^ 2 + γ ^ 2) -
      (5 / 2 - β) / ((5 / 2 - β) ^ 2 + γ ^ 2) := by
    simpa only using
      (MasulloRH.compensated_resolvent_baseline_pos β γ hβ0 hβ1 hheight)
  have hreal : (zeroResolventTerm (1 / 2) (3 : ℂ) ρ).re =
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
      ((3 - β) / ((3 - β) ^ 2 + γ ^ 2) -
       (5 / 2 - β) / ((5 / 2 - β) ^ 2 + γ ^ 2)) := by
    simp [zeroResolventTerm, β, γ, Complex.mul_re, Complex.sub_re,
      Complex.inv_re, Complex.normSq_apply, pow_two]
  rw [hreal]
  exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt hc0)
