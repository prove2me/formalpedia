-- Prove2me | solution 1 for Kyprianou.Ch02.finiteSmallBandCompensatedExponentAlgebraCh02V1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:32:34.059944+00:00
-- url     : https://prove2.me/submissions/5106f6e0-3a6a-4c96-97b5-37c2a1a65dff

import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
    (ν : Measure ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hfin : ν B < ⊤) (hsmall : ∀ x ∈ B, |x| < 1)
    (t ξ : ℝ) :
    Complex.exp (((-(t * ∫ x in B, x ∂ν) * ξ : ℝ) : ℂ) * Complex.I) *
      Complex.exp ((t : ℂ) * ∫ x in B,
        (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) =
      Complex.exp ((t : ℂ) * ∫ x in B,
        ProbabilityTheory.levyCompensatedIntegrand ξ x ∂ν) := by
  letI : IsFiniteMeasure (ν.restrict B) :=
    isFiniteMeasure_restrict.mpr hfin.ne
  let g : ℝ → ℂ := fun x => Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1
  let l : ℝ → ℂ := fun x => ((ξ : ℂ) * Complex.I) * (x : ℂ)
  let f := ProbabilityTheory.levyCompensatedIntegrand ξ
  have hg : Integrable g (ν.restrict B) := by
    apply Integrable.of_bound (by dsimp [g]; fun_prop) 2
    apply ae_of_all
    intro x
    calc
      ‖g x‖ ≤ ‖Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ)))‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp]; norm_num [Complex.mul_re]
  have hl : Integrable l (ν.restrict B) := by
    apply Integrable.of_bound (by dsimp [l]; fun_prop) |ξ|
    filter_upwards [ae_restrict_mem hB] with x hx
    simp only [l, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg ξ) (hsmall x hx).le
  have heq : f =ᵐ[ν.restrict B] fun x => g x - l x := by
    filter_upwards [ae_restrict_mem hB] with x hx
    have harg : Complex.I * (((ξ * x : ℝ) : ℂ)) =
        (x : ℂ) * (ξ : ℂ) * Complex.I := by
      push_cast
      ring
    simp [g, f, l, ProbabilityTheory.levyCompensatedIntegrand, hsmall x hx, harg]
    <;> ring
  change Complex.exp (((-(t * ∫ x in B, x ∂ν) * ξ : ℝ) : ℂ) * Complex.I) *
    Complex.exp ((t : ℂ) * ∫ x in B, g x ∂ν) =
      Complex.exp ((t : ℂ) * ∫ x in B, f x ∂ν)
  rw [← Complex.exp_add, integral_congr_ae heq, integral_sub hg hl]
  congr 1
  simp only [l, integral_const_mul]
  rw [integral_complex_ofReal (f := fun x : ℝ => x)]
  push_cast
  ring
