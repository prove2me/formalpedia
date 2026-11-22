-- Prove2me | solution 1 for MasulloRH.even_real_upper_right_omitted_sum_zero_for_interval_positive_test
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T20:18:26.273913+00:00
-- url     : https://prove2.me/submissions/b9f4a877-f17a-412c-822a-ba80585aa5cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_narrow_window_resolvent_cutoff_inequality_at_three
import Theorems.Thm_MasulloRH_regularized_arch_limit
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_MasulloRH_regularized_mellin_limit
import Theorems.Thm_MasulloRH_regularized_prime_limit
import Theorems.Thm_MasulloRH_regularized_spectral_limit
import Theorems.Thm_MasulloRH_single_resolvent_test
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open MasulloRH MeasureTheory Set Filter
open scoped Topology

-- The polar limit calculation follows the full-strip proof by davidloeffler
-- and the accepted endpoint adaptation df176fb8-4037-4112-be76-52bbcbea3294.
private theorem realPolarLimit :
    Tendsto (fun n : ℕ => cutoffPolar n (3 : ℂ)) atTop
      (𝓝 (regularizedPolar (3 : ℂ))) := by
  have hplus := regularized_mellin_limit (3 : ℂ) (1 / 2) (by norm_num) (by norm_num)
  have hminus := regularized_mellin_limit (3 : ℂ) (-1 / 2) (by norm_num) (by norm_num)
  convert hplus.add hminus using 1 <;>
    simp only [cutoffPolar, regularizedPolar] <;> congr 2 <;> ring

theorem solution
    (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (ψ : ℝ → ℝ) (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t)
    (hNonneg : ∀ t : ℝ, 0 ≤ ψ t)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hStrict : ∀ t : ℝ, 0 < ψ t ↔ t ≠ 1 ∧ (t - 1) ^ 2 / (1 + t ^ 2) < r)
    (hBoundary : ∀ z : ℂ, riemannZeta z = 0 → z.re = 1 / 2 + α → 0 < z.im → False) :
    ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im},
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (mellin (fun t => (ψ t : ℂ)) ((ρ : ℂ) - 1 / 2)).re = 0 := by
  have hThree : (3 / 2 : ℝ) < (3 : ℂ).re := by norm_num
  have hGeom := (regularized_arch_limit (3 : ℂ) hThree).add
    (regularized_prime_limit (3 : ℂ) hThree)
  have hSpec := realPolarLimit.sub (regularized_spectral_limit α hα hα2 (3 : ℂ) hThree)
  have hLimit :
      Tendsto (fun n : ℕ =>
        (cutoffArch n 3 + cutoffPrime n 3 - (cutoffPolar n 3 - cutoffSpectral α n 3)).re)
        atTop (𝓝 ((regularizedArch 3 + (-zetaLogDeriv 3 + zetaLogDeriv (5 / 2)) -
          (regularizedPolar 3 - regularizedSpectral α 3)).re)) :=
    (Complex.continuous_re.tendsto _).comp (hGeom.sub hSpec)
  have hPositive := ge_of_tendsto_of_frequently hLimit
    ((narrow_window_resolvent_cutoff_inequality_at_three α hα hα2 hBoundary).mono
      (fun n hn => sub_nonneg.mpr hn))
  have hScalar : (regularizedTraceRHS (1 / 2) 3).re ≤ (regularizedTraceRHS α 3).re := by
    rw [regularized_initial_identity_full_strip (3 : ℂ) hThree]
    simp only [regularizedTraceRHS, Complex.add_re, Complex.sub_re, Complex.neg_re] at hPositive ⊢
    linarith only [hPositive]
  have hWindow := (single_resolvent_test α).mp hScalar
  let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im}
  have : IsEmpty Z := ⟨fun z => by
    have hz0 : 0 < (z : ℂ).re := by linarith [z.property.2.1]
    have hz1 : (z : ℂ).re < 1 := z.property.2.2.1
    have hzwin : |(z : ℂ).re - 1 / 2| < 1 / 2 :=
      abs_lt.mpr ⟨by linarith, by linarith⟩
    have hz := (abs_lt.mp (hWindow ⟨z.val, z.property.1, hz0, hz1, hzwin⟩)).2
    linarith [z.property.2.1]⟩
  change ∑' ρ : Z, _ = 0
  exact tsum_empty
