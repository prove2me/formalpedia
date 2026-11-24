-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.positiveRoot_scale_pos_on_positives
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T21:34:38.786903+00:00
-- url     : https://prove2.me/submissions/9aa98e07-2f3c-4960-a9a4-e62081b0bc57

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
import Theorems.Thm_AvramDividend_Classical_psi_quadratic_upper
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_eventual_psi_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A positive q-root forces the q-scale to be strictly positive on the positive half-line. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (A : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : A.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction A q W)
    (a : ℝ) (ha : 0 < a) : 0 < W a := by
  let C0 : ℝ := |A.c| + A.σ ^ 2 / 2 +
    ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂A.ν
  let C : ℝ := |C0| + 1
  have hβ0 : 0 ≤ φ + 1 := by linarith
  have hψ : ∀ θ : ℝ, φ + 1 ≤ θ → q < A.ψ θ := by
    intro θ hθ
    have hφθ : φ < θ := by linarith
    have hθpos : 0 < θ := lt_trans hφ hφθ
    have hsec := levy_psi_positive_secant_monotone A φ θ hφ hφθ.le
    have hsecq : q / φ ≤ A.ψ θ / θ := by simpa [hroot] using hsec
    have hmul : (q / φ) * θ ≤ (A.ψ θ / θ) * θ :=
      mul_le_mul_of_nonneg_right hsecq hθpos.le
    have hcancel : (A.ψ θ / θ) * θ = A.ψ θ := by
      field_simp [ne_of_gt hθpos]
    have hupper : (q / φ) * θ ≤ A.ψ θ := by simpa [hcancel] using hmul
    have hlow : q < (q / φ) * θ := by
      field_simp [ne_of_gt hφ]
      nlinarith [mul_lt_mul_of_pos_left hφθ hq]
    exact hlow.trans_le hupper
  have hquad : ∀ θ : ℝ, φ + 1 ≤ θ →
      A.ψ θ - q ≤ C * (1 + θ ^ 2) := by
    intro θ hθ
    have hθ1 : 1 ≤ θ := by linarith [hφ, hθ]
    have hpsi_up := psi_quadratic_upper A θ hθ1
    have hle0 : A.ψ θ - q ≤ A.ψ θ := by linarith
    have hle1 : A.ψ θ - q ≤ C0 * θ ^ 2 := hle0.trans hpsi_up
    have hC0le : C0 ≤ C := by
      have hleabs : C0 ≤ |C0| := le_abs_self C0
      dsimp [C]
      linarith
    have hθsq : 0 ≤ θ ^ 2 := sq_nonneg θ
    have hle2 : C0 * θ ^ 2 ≤ C * θ ^ 2 :=
      mul_le_mul_of_nonneg_right hC0le hθsq
    have hCnonneg : 0 ≤ C := by
      dsimp [C]
      positivity
    have hle3 : C * θ ^ 2 ≤ C * (1 + θ ^ 2) := by nlinarith
    exact hle1.trans (hle2.trans hle3)
  exact scaleFunction_strict_pos_of_eventual_psi_bound
    A q W hW (φ + 1) C hβ0 hψ hquad a ha
