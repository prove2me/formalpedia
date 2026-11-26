-- Prove2me | solution 1 for Kyprianou.Ch04.geometricConvolutionNonnegativeSupport
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:46:17.034588+00:00
-- url     : https://prove2.me/submissions/10452938-8670-4425-b086-db2dfecf0ad3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_nonnegative_halfline_support_of_measure_convolution
import Theorems.Thm_Kyprianou_Ch04_convolutionPowerPreservesProbability
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Geometric convolution mixtures preserve nonnegative support. -/
theorem solution (eta mu : Measure ℝ) [IsProbabilityMeasure eta]
    (r : ENNReal) (h0 : eta (Iio 0) = 0)
    (hLaw : ∀ B : Set ℝ, MeasurableSet B →
      mu B = ∑' n : ℕ, ((1-r)*r^n) *
        ((Nat.rec (Measure.dirac (0 : ℝ)) (fun _ (m : Measure ℝ) => m.conv eta) n : Measure ℝ) B)) :
    mu (Iio 0) = 0 := by
  let m : ℕ → Measure ℝ := Nat.rec (Measure.dirac 0) (fun _ v => v.conv eta)
  have hp (n : ℕ) : IsProbabilityMeasure (m n) :=
    Kyprianou.Ch04.convolutionPowerPreservesProbability eta n
  have step (v : Measure ℝ) [IsProbabilityMeasure v] (hv : v (Iio 0) = 0) :
      (v.conv eta) (Iio 0) = 0 :=
    AvramDividend.Classical.nonnegative_halfline_support_of_measure_convolution v eta hv h0
  have hz (n : ℕ) : m n (Iio 0) = 0 := by
    induction n with
    | zero => simp [m,Measure.dirac_apply' _ measurableSet_Iio]
    | succ n ih =>
      change ((m n).conv eta) (Iio 0) = 0
      exact @step (m n) (hp n) ih
  rw [hLaw _ measurableSet_Iio]
  change (∑' n : ℕ, ((1-r)*r^n) * m n (Iio 0)) = 0
  simp_rw [hz,mul_zero,tsum_zero]
