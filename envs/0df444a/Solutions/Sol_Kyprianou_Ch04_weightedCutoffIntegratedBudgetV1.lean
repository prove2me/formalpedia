-- Prove2me | solution 1 for Kyprianou.Ch04.weightedCutoffIntegratedBudgetV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:01:56.567941+00:00
-- url     : https://prove2.me/submissions/685ae8d1-a3e9-4460-9997-4da184dd19c4

import Theorems.Thm_Kyprianou_Ch04_cutoffAEPointwiseBudgetV1
import Theorems.Thm_Kyprianou_Ch04_cutoffBandEnergiesV1
import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch04_integratedKernelBudgetV1
import Theorems.Thm_Kyprianou_Ch04_levyBandEnergyV1
import Theorems.Thm_Kyprianou_Ch04_cutoffPredictableIntegrandSquareBoundV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Integrate the actual two-cutoff kernel energy using the left-limit path budget. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) (hν : IsLevyMeasure ν)
    (a b K : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (hK : 0 ≤ K)
    (T : NNReal) (g : ℝ → ℝ → ℝ) (U V : NNReal → Ω → ℝ) (S : Ω → ℝ)
    (hG : ∀ s : ℝ, 0 ≤ s → Differentiable ℝ (g s))
    (hGbound : ∀ s x : ℝ, 0 ≤ s → |g s x| ≤ K)
    (hD : ∀ s x : ℝ, 0 ≤ s → |deriv (g s) x| ≤ K)
    (hS : Integrable S P) (hSnn : ∀ᵐ ω ∂P, 0 ≤ S ω)
    (hLeft : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → t ≤ T →
      (U t ω - V t ω)^2 ≤ S ω)
    (hEnergy : (∫ ω, S ω ∂P) ≤ 4 * (T : ℝ) *
      (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal) :
    (∫ ω, ∫ s in Ioc (0 : ℝ) (T : ℝ),
      ∫ z, (({w : ℝ | a < |w| ∧ |w| < 1}).indicator
          (fun w => w * g s (U s.toNNReal ω)) z -
        ({w : ℝ | b < |w| ∧ |w| < 1}).indicator
          (fun w => w * g s (V s.toNNReal ω)) z)^2 ∂ν ∂volume ∂P) ≤
      (K^2 * (T : ℝ) * (1 + 4 * (T : ℝ) *
        (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal)) *
        (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal := by
  let A : Set ℝ := {z | a < |z| ∧ |z| ≤ b ∧ |z| < 1}
  let B : Set ℝ := {z | b < |z| ∧ |z| < 1}
  let C : Set ℝ := {z | |z| ≤ b}
  let D : Set ℝ := {z | |z| < 1}
  let q := (∫⁻ z in C, ENNReal.ofReal (z^2) ∂ν).toReal
  let Q := (∫⁻ z in D, ENNReal.ofReal (z^2) ∂ν).toReal
  let H (s z : ℝ) (ω : Ω) :=
    ({w : ℝ | a < |w| ∧ |w| < 1}).indicator
      (fun w => w * g s (U s.toNNReal ω)) z -
    B.indicator (fun w => w * g s (V s.toNNReal ω)) z
  obtain ⟨hAb,hBb⟩ := Kyprianou.Ch04.cutoffBandEnergiesV1 ν hν a b ha hab hb
  have hp := Kyprianou.Ch04.cutoffAEPointwiseBudgetV1 P ν hν a b K ha hab hb hK
    T g U V S hG hGbound hD hLeft
  have hS0 : 0 ≤ ∫ ω, S ω ∂P := integral_nonneg_of_ae hSnn
  have hqQ := Kyprianou.Ch04.integratedKernelBudgetV1 P ν T H S
    (A.indicator (fun z => z^2)) (B.indicator (fun z => z^2)) hAb.1 hBb.1 hS K hp
  calc
    _ ≤ K^2 * (T : ℝ) * ((∫ z, A.indicator (fun z => z^2) z ∂ν) +
        (∫ z, B.indicator (fun z => z^2) z ∂ν) * ∫ ω, S ω ∂P) := hqQ
    _ ≤ K^2 * (T : ℝ) * (q + Q * (4 * (T : ℝ) * q)) :=
      mul_le_mul_of_nonneg_left (add_le_add hAb.2.2
        (mul_le_mul hBb.2.2 hEnergy hS0 ENNReal.toReal_nonneg)) (by positivity)
    _ = _ := by dsimp [q,Q,C,D]; ring
