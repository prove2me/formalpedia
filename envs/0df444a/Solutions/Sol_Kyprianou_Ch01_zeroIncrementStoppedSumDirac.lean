-- Prove2me | solution 1 for Kyprianou.Ch01.zeroIncrementStoppedSumDirac
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:30:47.157071+00:00
-- url     : https://prove2.me/submissions/05275177-3ab7-4ef0-9212-1708b886084a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option autoImplicit false

/-! If all IID marginal increment laws are Dirac zero, every stopped sum is Dirac zero. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ) (N : Ω → ℕ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hCommon : ∀ n : ℕ, HasLaw (increment n) jumpLaw P)
    (hDirac : jumpLaw = Measure.dirac (0 : ℝ)) :
    P.map (fun ω =>
      ∑ i ∈ Finset.range (N ω), increment i ω) =
      Measure.dirac (0 : ℝ) := by
  have heach : ∀ n : ℕ, ∀ᵐ ω ∂P, increment n ω = 0 := by
    intro n
    have h := hCommon n
    rw [hDirac] at h
    exact h.ae_eq_of_dirac
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, increment n ω = 0 :=
    (ae_all_iff).2 heach
  have hzero :
      (fun ω => ∑ i ∈ Finset.range (N ω), increment i ω)
        =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
    filter_upwards [hall] with ω hω
    simp [hω]
  calc
    P.map (fun ω => ∑ i ∈ Finset.range (N ω), increment i ω) =
      P.map (fun _ : Ω => (0 : ℝ)) := Measure.map_congr hzero
    _ = Measure.dirac (0 : ℝ) := by
      rw [Measure.map_const]
      simp
