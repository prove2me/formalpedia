-- Prove2me | solution 1 for Kyprianou.Ch01.firstWeakDescendingRenewalPotential
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:08:26.307282+00:00
-- url     : https://prove2.me/submissions/a9b4427d-3510-4781-8b05-6ffd367b28e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Theorems.Thm_Kyprianou_Ch01_weakDescendingFirstPassagePartition
import Theorems.Thm_Kyprianou_Ch01_weakDescendingStoppedConvolution
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (increment n))
    (hindep : iIndepFun increment P)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hLaw : ∀ n : ℕ, HasLaw (increment n) mu P) :
    let S : ℕ → Ω → ℝ :=
      fun n ω => ∑ i ∈ Finset.range n, increment i ω
    ∀ B : Set ℝ, MeasurableSet B →
      B ⊆ Set.Iic (0 : ℝ) →
        P {ω | ∃ n : ℕ, 1 ≤ n ∧ S n ω ∈ B ∧
          ∀ j : ℕ, 1 ≤ j → j < n → 0 < S j ω} =
          ∑' n : ℕ,
            ∫⁻ y : ℝ, mu
              ((fun z : ℝ => y + z) ⁻¹' B) ∂
              (Measure.map (S n)
                (P.restrict {ω | ∀ j : ℕ,
                    1 ≤ j → j ≤ n → 0 < S j ω})) := by
  intro S B hB hsubset
  calc
    P {ω | ∃ n : ℕ, 1 ≤ n ∧ S n ω ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j < n → 0 < S j ω}
      = ∑' n : ℕ,
          P {ω | S (n + 1) ω ∈ B ∧
            ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω} := by
        exact Kyprianou.Ch01.weakDescendingFirstPassagePartition
          P increment hmeas B hB hsubset
    _ = ∑' n : ℕ, ∫⁻ y : ℝ,
          mu ((fun z : ℝ => y + z) ⁻¹' B) ∂
          (Measure.map (S n)
            (P.restrict {ω | ∀ j : ℕ,
              1 ≤ j → j ≤ n → 0 < S j ω})) := by
        congr 1
        funext n
        exact Kyprianou.Ch01.weakDescendingStoppedConvolution
          P increment hmeas hindep mu hLaw n B hB
