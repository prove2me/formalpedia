-- Prove2me | solution 1 for Kyprianou.Ch01.expConvolutionPowerGammaDensity
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:23:24.727217+00:00
-- url     : https://prove2.me/submissions/37c6b3b0-df06-4ed9-bd08-b4f57e6e2ac4

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.WithDensity
import Definitions.Def_QueueingFundamentals_MG1_transforms
import Definitions.Def_levy_foundations_arrivalGammaDensity
import Theorems.Thm_levy_foundations_arrivalGammaDensityConvolution
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace CPGAux

theorem conv_withDensity (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (volume.withDensity f).conv (volume.withDensity g) =
      volume.withDensity (fun z => ∫⁻ x, f x * g (z - x)) := by
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator_one hs,
    Measure.lintegral_conv (measurable_one.indicator hs)]
  rw [lintegral_withDensity_eq_lintegral_mul _ hf (by
    exact Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ => s.indicator 1 (p.1 + p.2))
      ((measurable_one.indicator hs).comp measurable_add))]
  have h1 : ∀ x, ∫⁻ y, s.indicator 1 (x + y) ∂(volume.withDensity g) =
      ∫⁻ y, g y * s.indicator 1 (x + y) := by
    intro x
    exact lintegral_withDensity_eq_lintegral_mul _ hg
      ((measurable_one.indicator hs).comp (measurable_const_add x))
  simp_rw [h1]
  rw [← lintegral_indicator hs]
  have h2 : ∀ z, s.indicator (fun z => ∫⁻ x, f x * g (z - x)) z =
      ∫⁻ x, s.indicator 1 z * (f x * g (z - x)) := by
    intro z
    rw [lintegral_const_mul _ (by fun_prop)]
    by_cases hz : z ∈ s <;> simp [hz]
  simp_rw [h2]
  rw [lintegral_lintegral_swap (by
    apply Measurable.aemeasurable
    apply Measurable.mul
    · exact (measurable_one.indicator hs).comp measurable_fst
    · exact (hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd)))]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  have h3 : ∫⁻ z, s.indicator 1 z * (f x * g (z - x)) =
      f x * ∫⁻ z, g (z - x) * s.indicator 1 z := by
    rw [← lintegral_const_mul _ (by
      exact (hg.comp (measurable_id.sub measurable_const)).mul (measurable_one.indicator hs))]
    congr 1; funext z; ring
  rw [h3]
  congr 1
  rw [← lintegral_add_right_eq_self (fun z => g (z - x) * s.indicator 1 z) x]
  congr 1; funext y; simp [add_comm]

theorem meas_gamma (beta : ℝ) (n : ℕ) : Measurable (LevyFoundations.arrivalGammaDensity beta n) := by
  unfold LevyFoundations.arrivalGammaDensity LevyFoundations.arrivalGammaDensityReal
  exact Measurable.indicator (by fun_prop) measurableSet_Ici

end CPGAux

theorem solution
    (beta : ℝ) (hbeta : 0 < beta) :
    let mu : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * x)))
    ∀ n : ℕ, QueueingFundamentals.MG1.convPow mu (n + 1) =
      volume.withDensity (LevyFoundations.arrivalGammaDensity beta n) := by
  intro mu
  have hmu : mu = volume.withDensity (LevyFoundations.arrivalGammaDensity beta 0) := by
    simp only [mu]
    unfold LevyFoundations.arrivalGammaDensity
    rw [withDensity_indicator measurableSet_Ici, Measure.restrict_congr_set Ioi_ae_eq_Ici]
    congr 1
    funext x
    simp [LevyFoundations.arrivalGammaDensityReal]
  intro n
  induction n with
  | zero =>
    show (QueueingFundamentals.MG1.convPow mu 0).conv mu = _
    simp only [QueueingFundamentals.MG1.convPow]
    rw [Measure.dirac_zero_conv, hmu]
  | succ k ih =>
    show (QueueingFundamentals.MG1.convPow mu (k + 1)).conv mu = _
    rw [ih]
    conv_lhs => rw [hmu]
    rw [CPGAux.conv_withDensity _ _ (CPGAux.meas_gamma beta k) (CPGAux.meas_gamma beta 0)]
    congr 1
    funext z
    exact levy_foundations_arrivalGammaDensityConvolution hbeta k z
