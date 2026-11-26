-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49RenewalLawSeriesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:36:51.588882+00:00
-- url     : https://prove2.me/submissions/8c51ff97-5655-4b81-b25b-461f676cd397

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49RenewalConvolutionStepV1
import Theorems.Thm_Kyprianou_Ch04_convolutionPowerPreservesProbability
import Theorems.Thm_Kyprianou_Ch04_exercise49GeometricSeriesV2
open MeasureTheory Set Filter
open scoped ENNReal NNReal
set_option autoImplicit false
/-- Iterate the renewal measure equation and use the proved geometric remainder lemma. -/
theorem solution
    (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho < 1)
    (mu eta : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure eta]
    (hLaw : mu = ENNReal.ofReal (1 - rho) • Measure.dirac 0 +
      ENNReal.ofReal rho • (mu.conv eta)) (B : Set ℝ) (hB : MeasurableSet B) :
    let convPow : Nat → Measure ℝ :=
      Nat.rec (Measure.dirac (0 : ℝ)) (fun _ nu => nu.conv eta)
    (mu B).toReal = (1 - rho) * ∑' k : Nat, rho ^ k * (convPow k B).toReal := by
  let cp : ℕ → Measure ℝ :=
    Nat.rec (Measure.dirac (0 : ℝ)) (fun _ nu => nu.conv eta)
  have hp (n : ℕ) : IsProbabilityMeasure (cp n) :=
    Kyprianou.Ch04.convolutionPowerPreservesProbability eta n
  let r (n : ℕ) : ℝ := rho ^ n * (mu.conv (cp n) B).toReal
  have hmass (n : ℕ) : 0 ≤ r n ∧ r n ≤ rho ^ n := by
    have hpr := @Measure.probabilitymeasure_of_probabilitymeasures_conv ℝ _ _
      mu (cp n) _ inferInstance (hp n)
    have hle : mu.conv (cp n) B ≤ 1 := by
      calc
        _ ≤ mu.conv (cp n) univ := measure_mono (subset_univ _)
        _ = 1 := @measure_univ ℝ _ (mu.conv (cp n)) hpr
    have hr : (mu.conv (cp n) B).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) hle
    exact ⟨mul_nonneg (pow_nonneg h0 _) ENNReal.toReal_nonneg,
      mul_le_of_le_one_right (pow_nonneg h0 _) hr⟩
  have hrec (n : ℕ) : r n =
      (1 - rho) * (rho ^ n * (cp n B).toReal) + r (n + 1) := by
    have hval : (mu.conv (cp n) B).toReal =
        (1 - rho) * (cp n B).toReal + rho * (mu.conv (cp (n + 1)) B).toReal :=
      @Kyprianou.Ch04.exercise49RenewalConvolutionStepV1 rho h0 h1 mu eta
        (cp n) inferInstance inferInstance (hp n) hLaw B
    unfold r
    rw [hval, pow_succ]
    ring
  have hseries := Kyprianou.Ch04.exercise49GeometricSeriesV2 rho h0 h1
    (fun n => (cp n B).toReal) r (fun _ => ENNReal.toReal_nonneg) hmass hrec
  have hz : r 0 = (mu B).toReal := by
    unfold r cp
    rw [pow_zero, one_mul]
    change (mu.conv (Measure.dirac (0 : ℝ)) B).toReal = (mu B).toReal
    rw [Measure.conv_dirac]
    simp
  rw [hz] at hseries
  exact hseries
