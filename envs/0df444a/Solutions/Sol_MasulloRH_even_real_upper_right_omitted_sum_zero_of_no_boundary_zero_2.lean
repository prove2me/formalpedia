-- Prove2me | solution 2 for MasulloRH.even_real_upper_right_omitted_sum_zero_of_no_boundary_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:16:46.181845+00:00
-- url     : https://prove2.me/submissions/cd1b3c49-77e7-4f42-82b5-9f4d56e94619
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
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t)
    (hBoundary : ∀ z : ℂ, riemannZeta z = 0 → z.re = 1 / 2 + α → 0 < z.im → False) :
    ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im},
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (mellin (fun t => (ψ t : ℂ)) ((ρ : ℂ) - 1 / 2)).re = 0 :=
  haveI : IsEmpty {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im} :=
    ⟨fun ρ => by
      have hre : (ρ : ℂ).re = 1 / 2 :=
        riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis (ρ : ℂ)
          ρ.2.1 (by linarith [ρ.2.2.1]) ρ.2.2.2.1
      linarith [ρ.2.2.1]⟩
  tsum_empty
