-- Prove2me | solution 1 for MasulloAudit.trace_formula_rational_window_mono
-- status  : ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:51:34.271902+00:00
-- url     : https://prove2.me/submissions/72c5dc5d-f725-4504-b43d-4b4ac70a8a02

import Theorems.Thm_MasulloAudit_trace_formula_rational_fixed_window_iff

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

open MasulloRH

theorem solution (α α' : ℝ) (hα : 0 < α) (hαα' : α ≤ α')
    (h : ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) :
    ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ α') ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α', zetaTraceTerm φ α' ρ := by
  have hzeros := (MasulloAudit.trace_formula_rational_fixed_window_iff α hα).1 h
  exact (MasulloAudit.trace_formula_rational_fixed_window_iff α' (lt_of_lt_of_le hα hαα')).2
    fun ρ => lt_of_lt_of_le (hzeros ρ) hαα'

