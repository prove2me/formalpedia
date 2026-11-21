-- Prove2me | solution 1 for MasulloAudit.window_remainder_ne_zero_of_omitted_zero
-- status  : ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-21T00:48:43.550841+00:00
-- url     : https://prove2.me/submissions/b4269195-134d-45cf-bf48-18a5d6dd27fb

import Definitions.Def_MasulloRH_RationalTrace
import Theorems.Thm_MasulloAudit_trace_formula_window_with_remainder
import Theorems.Thm_MasulloAudit_trace_formula_rational_fixed_window_iff

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

open MasulloRH

theorem solution (α : ℝ) (hα : 0 < α)
    (ρ₀ : ZetaZerosInTraceStrip (1 / 2)) (hρ₀ : α ≤ |(ρ₀ : ℂ).re - 1 / 2|) :
    ∃ φ : ℝ → ℂ, IsRationalTraceTest φ ∧
      (∑' ρ : {ρ : ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|},
        zetaTraceTerm φ (1 / 2) ρ) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hwin := (MasulloAudit.trace_formula_rational_fixed_window_iff α hα).1 (by
    intro φ hφ
    obtain ⟨h1, h2, h3, _, h5⟩ :=
      MasulloAudit.trace_formula_window_with_remainder α φ hφ
    refine ⟨h1, h2, h3, ?_⟩
    rw [h5, hcon φ hφ, sub_zero])
  exact absurd hρ₀ (not_le.mpr (hwin ρ₀))

