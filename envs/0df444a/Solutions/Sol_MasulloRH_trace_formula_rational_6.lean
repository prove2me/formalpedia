-- Prove2me | solution 6 for MasulloRH.trace_formula_rational
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T23:11:14.92904+00:00
-- url     : https://prove2.me/submissions/6d29b9df-bcb8-4080-8d39-8deb601051d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_ConnesRZ_weil_defs
import Theorems.Thm_MasulloRH_trace_formula_rational_full_strip
import Theorems.Thm_MasulloRH_narrow_window_omitted_zero_sum
import Theorems.Thm_MasulloRH_spectral_trace_hasSum_iff_omitted_sum_zero
import Theorems.Thm_MasulloAudit_trace_formula_rational_of_half_le

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology
open MasulloRH

theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ)
    (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  by_cases hlarge : 1 / 2 ≤ α
  · exact MasulloAudit.trace_formula_rational_of_half_le α hlarge φ hφ
  · have hsmall : α < 1 / 2 := lt_of_not_ge hlarge
    have hfull := trace_formula_rational_full_strip φ hφ
    have hOmit := narrow_window_omitted_zero_sum α hα hsmall φ hφ
    have hHas :=
      (spectral_trace_hasSum_iff_omitted_sum_zero α φ hφ).2 hOmit
    rcases hfull with ⟨hInt, hPrime, _hFullSpec, _hFullEq⟩
    refine ⟨hInt, hPrime, hHas.summable, ?_⟩
    rw [hHas.tsum_eq]
    ring
