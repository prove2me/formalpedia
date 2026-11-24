-- Prove2me | solution 1 for Kyprianou.Ch02.levyBVExponentialGridPowerLowerBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:12:07.458798+00:00
-- url     : https://prove2.me/submissions/9c72980d-7eb0-4a6c-8432-65c80d136f6b

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_aeBVUniformGridAbsoluteSumsBoundedV1
import Theorems.Thm_Kyprianou_Ch02_positiveExpectedExponentialLowerBoundOfAEUniformSumsV1
import Theorems.Thm_Kyprianou_Ch02_levyUniformGridExponentialAbsoluteSumExpectationV1
open MeasureTheory ProbabilityTheory Set Function Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    (∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) →
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ,
        c ≤ (∫ ω, Real.exp (-|X (((n : ℝ≥0) + 1)⁻¹) ω|) ∂P) ^ (n + 1) := by
  intro hBV
  let S (n : ℕ) (ω : Ω) : ℝ := ∑ i : Fin (n + 1),
    |X (((i.val + 1 : ℕ) : ℝ≥0) * (((n : ℝ≥0) + 1)⁻¹)) ω -
     X ((i.val : ℝ≥0) * (((n : ℝ≥0) + 1)⁻¹)) ω|
  have hcoord := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  have hm (n : ℕ) : AEMeasurable (S n) P := by
    change AEMeasurable (fun ω => ∑ i : Fin (n + 1),
      |X (((i.val + 1 : ℕ) : ℝ≥0) * (((n : ℝ≥0) + 1)⁻¹)) ω -
       X ((i.val : ℝ≥0) * (((n : ℝ≥0) + 1)⁻¹)) ω|) P
    let F (i : Fin (n + 1)) (ω : Ω) :=
      |X (((i.val + 1 : ℕ) : ℝ≥0) * (((n : ℝ≥0) + 1)⁻¹)) ω -
       X ((i.val : ℝ≥0) * (((n : ℝ≥0) + 1)⁻¹)) ω|
    have hF (i : Fin (n + 1)) : AEMeasurable (F i) P :=
      ((hcoord _).sub (hcoord _)).abs
    change AEMeasurable (fun ω => ∑ i : Fin (n + 1), F i ω) P
    exact Finset.aemeasurable_fun_sum Finset.univ (fun i _ => hF i)
  have hn (n : ℕ) (ω : Ω) : 0 ≤ S n ω :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  obtain ⟨c, hc, hbound⟩ :=
    Kyprianou.Ch02.positiveExpectedExponentialLowerBoundOfAEUniformSumsV1
      P S hm hn (Kyprianou.Ch02.aeBVUniformGridAbsoluteSumsBoundedV1 P X hBV)
  refine ⟨c, hc, fun n => ?_⟩
  have hs := Kyprianou.Ch02.levyUniformGridExponentialAbsoluteSumExpectationV1 P X hX n
  rw [← hs]
  exact hbound n
