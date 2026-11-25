-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46GeometricConvolutionLaplaceV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:59:16.013573+00:00
-- url     : https://prove2.me/submissions/32c52396-35cb-49e9-bcca-b52dafdcaab0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_positive_laplace_functional_convolution
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (eta nu : Measure Real) [IsProbabilityMeasure eta]
    (r : ENNReal) (s : Real)
    (hLaw : ∀ B : Set Real, MeasurableSet B →
      nu B = ∑' n : Nat, ((1-r)*r^n) *
        ((Nat.rec (Measure.dirac (0 : Real)) (fun _ (m : Measure Real) => m.conv eta) n : Measure Real) B)) :
    (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-s*x)) ∂nu) =
      (1-r) * (1-r*(∫⁻ x : Real, ENNReal.ofReal (Real.exp (-s*x)) ∂eta))⁻¹ := by
  let m : Nat → Measure Real := Nat.rec (Measure.dirac 0) (fun _ v => v.conv eta)
  let f : Real → ENNReal := fun x => ENNReal.ofReal (Real.exp (-s*x))
  let z := ∫⁻ x, f x ∂eta
  have hpow (n : Nat) : (∫⁻ x, f x ∂m n) = z^n := by
    induction n with
    | zero => simp [m, f, lintegral_dirac]
    | succ n ih =>
      change (∫⁻ x, f x ∂(m n).conv eta) = _
      rw [AvramDividend.Classical.positive_laplace_functional_convolution (m n) eta s,
        ih, pow_succ]
  have hsum : nu = Measure.sum (fun n : Nat => ((1-r)*r^n) • m n) := by
    ext B hB
    rw [Measure.sum_apply _ hB, hLaw B hB]
    rfl
  change (∫⁻ x, f x ∂nu) = (1-r)*(1-r*z)⁻¹
  rw [hsum, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul, hpow, mul_assoc, ← mul_pow]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
