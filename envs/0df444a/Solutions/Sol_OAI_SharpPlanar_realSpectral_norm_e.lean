-- Prove2me | solution 1 for OAI.SharpPlanar.realSpectral_norm_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:11:16.575083+00:00
-- url     : https://prove2.me/submissions/165b5895-dda2-40a2-bf0d-79368ed8896e

import Mathlib

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal interpolation

The folded spectral representation gives the cardinal values and derivatives.
Gaussian damping then extends the radial cardinal functions to Schwartz functions.
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory



open MeasureTheory
open scoped ComplexConjugate



open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

namespace SharpPlanar
open MeasureTheory Set

lemma realSpectral_norm_e_oai (ell : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (s : ℝ) :
    ‖(Complex.I*Real.pi*(t:ℂ))^ell * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ ≤ Real.pi^ell := by
  have he : ‖Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [norm_mul, norm_pow, he, mul_one]
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos Real.pi_pos,abs_of_nonneg ht.1]
  exact mul_le_of_le_one_right Real.pi_pos.le ht.2

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.realSpectral_norm_e_oai := @OAI.SharpPlanar.realSpectral_norm_e_oai
