-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagOfLocallyFiniteStepRepresentationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:46:37.69439+00:00
-- url     : https://prove2.me/submissions/b6a0fe33-41be-4886-bfeb-ed2e8ae2b186

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_finiteRegionStepSumCadlagNNRealV1
import Theorems.Thm_ProbabilityTheory_IsCadlagAt_congr

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (hlocal : ∀ T : ℕ, ∃ (s : Finset (ℝ × ℝ))
      (weight : ℝ × ℝ → ℝ), ∀ t : ℝ≥0, t ≤ (T : ℝ≥0) →
      f t = ∑ p ∈ s, if p.1 ≤ (t : ℝ) then weight p else 0) :
    ProbabilityTheory.IsCadlag f := by
  intro t
  obtain ⟨T, hT⟩ := exists_nat_gt (t : ℝ)
  have hreal : (t : ℝ) < ((T : ℝ≥0) : ℝ) := by simpa using hT
  have hnn : t < (T : ℝ≥0) := NNReal.coe_lt_coe.mp hreal
  obtain ⟨s, weight, hs⟩ := hlocal T
  have hstep := Kyprianou.Ch02.finiteRegionStepSumCadlagNNRealV1 s weight
  apply (hstep t).congr
  filter_upwards [isOpen_Iio.mem_nhds hnn] with u hu
  exact (hs u (le_of_lt hu)).symm
