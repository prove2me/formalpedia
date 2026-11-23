-- Prove2me | solution 2 for MasulloRH.even_real_upper_right_omitted_sum_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:16:49.16686+00:00
-- url     : https://prove2.me/submissions/c4c8e16a-9119-4626-a017-15304a23aac8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RationalTrace
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

open MasulloRH MeasureTheory Set
set_option autoImplicit false
namespace MasulloRH
end MasulloRH
open MasulloRH

theorem solution
    (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (ψ : ℝ → ℝ) (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t) :
    ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im},
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (mellin (fun t => (ψ t : ℂ)) ((ρ : ℂ) - 1 / 2)).re = 0 :=
  by
    -- The Riemann hypothesis in its open-strip form.
    have hstrip : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 :=
      riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis
    -- No zero has real part in `[1/2 + α, 1)`: the index type of the sum is empty.
    haveI hempty :
        IsEmpty {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im} := by
      refine ⟨fun ρ => ?_⟩
      obtain ⟨hz, hge, hlt, _⟩ := ρ.2
      have hre : (ρ : ℂ).re = 1 / 2 := hstrip (ρ : ℂ) hz (by linarith) hlt
      linarith
    -- A sum over an empty index type is zero.
    exact tsum_empty
