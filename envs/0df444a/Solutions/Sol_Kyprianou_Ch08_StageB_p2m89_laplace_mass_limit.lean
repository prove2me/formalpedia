-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_laplace_mass_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:02:04.531822+00:00
-- url     : https://prove2.me/submissions/d95610ea-cf5d-43c5-90cd-0faa24a68024

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem solution
    (ν : Measure ℝ) (hsupp : ν (Iio (0 : ℝ)) = 0) :
    Tendsto (fun n : ℕ => ∫⁻ y, ENNReal.ofReal
      (Real.exp (-(1 / ((n : ℝ) + 1)) * y)) ∂ν) atTop (𝓝 (ν univ)) := by
  let s (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hlim : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let f (n : ℕ) (y : ℝ) := ENNReal.ofReal (Real.exp (-s n * y))
  have hf (n : ℕ) : Measurable (f n) := by dsimp [f]; fun_prop
  have hae : ∀ᵐ y ∂ν, 0 ≤ y := by rw [ae_iff]; simpa only [not_le, Set.Iio] using hsupp
  have hanti (n : ℕ) : s n.succ ≤ s n := by
    dsimp [s]
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith
  have hm (n : ℕ) : ∀ᵐ y ∂ν, f n y ≤ f n.succ y := by
    filter_upwards [hae] with y hy
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (by nlinarith [mul_nonneg (sub_nonneg.mpr (hanti n)) hy]))
  have hi : ∀ᵐ y ∂ν, (⨆ n, f n y) = 1 := by
    filter_upwards [hae] with y hy
    have ht : Tendsto (fun n => f n y) atTop (𝓝 1) := by
      simpa [f] using ENNReal.tendsto_ofReal
        (Real.continuous_exp.continuousAt.tendsto.comp (hlim.neg.mul_const y))
    have hmono : Monotone (fun n => f n y) := monotone_nat_of_le_succ fun n => by
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (by nlinarith [mul_nonneg (sub_nonneg.mpr (hanti n)) hy]))
    exact tendsto_nhds_unique (tendsto_atTop_iSup hmono) ht
  have hmass : (⨆ n, ∫⁻ y, f n y ∂ν) = ν univ := by
    rw [← lintegral_iSup_ae hf hm, lintegral_congr_ae hi, lintegral_one]
  change Tendsto (fun n => ∫⁻ y, f n y ∂ν) atTop (𝓝 (ν univ))
  rw [← hmass]
  exact tendsto_atTop_iSup (monotone_nat_of_le_succ fun n => lintegral_mono_ae (hm n))
