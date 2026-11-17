-- Prove2me | solution 1 for Kyprianou.Ch01.zeroCountStoppedWalkEqDirac
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:52:39.550175+00:00
-- url     : https://prove2.me/submissions/bffbbfa1-8d01-41fb-afe3-6cc644217ccf

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

/-! If the random stopping count is zero almost surely, the stopped sum is Dirac zero. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hNzero : P {ω | N ω = 0} = 1) :
    P.map (fun ω =>
      ∑ i ∈ Finset.range (N ω), increment i ω) =
      Measure.dirac (0 : ℝ) := by
  have hs : MeasurableSet {ω | N ω = 0} :=
    hNmeas (measurableSet_singleton 0)
  have hzero : P {ω | N ω ≠ 0} = 0 := by
    have hcomp := prob_compl_eq_one_sub (μ := P) hs
    change P ({ω | N ω = 0}ᶜ) = 0
    simpa [hNzero] using hcomp
  have hae : ∀ᵐ ω ∂P, N ω = 0 := by
    rw [ae_iff]
    exact hzero
  have hf :
      (fun ω => ∑ i ∈ Finset.range (N ω), increment i ω)
        =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
    filter_upwards [hae] with ω hω
    simp [hω]
  calc
    P.map (fun ω => ∑ i ∈ Finset.range (N ω), increment i ω) =
        P.map (fun _ : Ω => (0 : ℝ)) :=
          Measure.map_congr hf
    _ = Measure.dirac (0 : ℝ) := by
      rw [Measure.map_const]
      simp
