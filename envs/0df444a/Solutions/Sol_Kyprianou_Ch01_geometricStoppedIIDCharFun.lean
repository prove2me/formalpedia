-- Prove2me | solution 1 for Kyprianou.Ch01.geometricStoppedIIDCharFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:43:35.576737+00:00
-- url     : https://prove2.me/submissions/bb1a0c58-2043-4a93-aaf9-d406cd21f4f4

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_randomCountIndependentSumCharFunMixture
import Theorems.Thm_Kyprianou_Ch01_iidFixedLengthCharFun
import Theorems.Thm_Kyprianou_Ch01_geometricFourierTsum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-! Exact stopped-geometric characteristic function from conditional Fourier mixture. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIID : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hCommon : ∀ n : ℕ,
      HasLaw (increment n) jumpLaw P)
    (hGeometric : ∀ k : ℕ,
      P {ω | N ω = k} =
        ENNReal.ofReal (p * (1 - p) ^ k))
    (hIndependent : IndepFun N
      (fun ω => fun n : ℕ => increment n ω) P) :
    ∀ xi : ℝ,
      charFun (P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω)) xi =
        (p : ℂ) / (1 - (((1 - p : ℝ) : ℂ) * charFun jumpLaw xi)) := by
  intro xi
  have hsum := Kyprianou.Ch01.randomCountIndependentSumCharFunMixture
    P increment N hNmeas hIncMeas hIndependent xi
  rw [hsum]
  have hq0 : 0 ≤ 1 - p := le_of_lt (sub_pos.mpr hp1)
  have hz : ‖charFun jumpLaw xi‖ ≤ 1 :=
    MeasureTheory.norm_charFun_le_one xi
  calc
    (∑' n : ℕ,
        ((P {ω | N ω = n}).toReal : ℂ) *
          charFun (P.map (fun ω =>
            ∑ i ∈ Finset.range n, increment i ω)) xi) =
      ∑' n : ℕ,
        ((p * (1 - p) ^ n : ℝ) : ℂ) *
          (charFun jumpLaw xi) ^ n := by
        apply tsum_congr
        intro n
        rw [Kyprianou.Ch01.iidFixedLengthCharFun
          P increment hIncMeas hIID jumpLaw hCommon n xi]
        rw [hGeometric n, ENNReal.toReal_ofReal (by positivity)]
    _ = ∑' n : ℕ,
        (p : ℂ) * ((((1 - p : ℝ) : ℂ) * charFun jumpLaw xi) ^ n) := by
          apply tsum_congr
          intro n
          push_cast
          rw [mul_pow]
          ring
    _ = (p : ℂ) / (1 - (((1 - p : ℝ) : ℂ) * charFun jumpLaw xi)) :=
      Kyprianou.Ch01.geometricFourierTsum p hp0 hp1 (charFun jumpLaw xi) hz
