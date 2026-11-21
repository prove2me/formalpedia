-- Prove2me | solution 4 for MasulloRH.narrow_window_omitted_zero_sum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-21T00:37:03.765694+00:00
-- url     : https://prove2.me/submissions/3b385c19-453d-45f4-b41d-f9003a6428c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_trace_formula_rational
import Theorems.Thm_MasulloAudit_trace_formula_rational_fixed_window_iff
import Definitions.Def_ConnesRZ_weil_defs

open MeasureTheory Set MasulloRH ConnesRZ

theorem solution (α : ℝ) (hα : 0 < α) (hsmall : α < 1/2)
    (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
    (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0 := by
  -- Theorem 12.5.1.1 at the window α, fed into the fixed-window iff, puts every zero in the window.
  have hall := (MasulloAudit.trace_formula_rational_fixed_window_iff α hα).1
    (fun ψ hψ => MasulloRH.trace_formula_rational α hα ψ hψ)
  intro omitted
  have : IsEmpty omitted := ⟨fun r => by
    obtain ⟨⟨z, hz⟩, hr⟩ := r
    have hz' : riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 := hz
    have hlt := hall ⟨z, hz'.1, hz'.2.1, hz'.2.2,
      by rw [abs_lt]; constructor <;> linarith [hz'.2.1, hz'.2.2]⟩
    exact absurd hr (not_le.2 hlt)⟩
  exact tsum_empty
