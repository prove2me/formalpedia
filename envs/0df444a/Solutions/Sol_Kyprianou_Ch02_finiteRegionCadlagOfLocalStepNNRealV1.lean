-- Prove2me | solution 1 for Kyprianou.Ch02.finiteRegionCadlagOfLocalStepNNRealV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:47:31.295226+00:00
-- url     : https://prove2.me/submissions/596b1eb5-5758-4e8c-befb-2d5d867b0160

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_finiteRegionStepSumCadlagNNRealV1
import Theorems.Thm_ProbabilityTheory_IsCadlagAt_congr
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ)
    (hlocal : ∀ (t : ℝ≥0), ∃ T : ℝ≥0, t < T ∧
      ∃ (s : Finset (ℝ × ℝ)) (w : ℝ × ℝ → ℝ),
        ∀ u : ℝ≥0, u < T →
          f u = ∑ p ∈ s, if p.1 ≤ (u : ℝ) then w p else 0) :
    ProbabilityTheory.IsCadlag f := by
  intro t
  obtain ⟨T, hT, s, w, hEq⟩ := hlocal t
  have hs : ProbabilityTheory.IsCadlag
      (fun u : ℝ≥0 => ∑ p ∈ s, if p.1 ≤ (u : ℝ) then w p else 0) :=
    Kyprianou.Ch02.finiteRegionStepSumCadlagNNRealV1 s w
  refine (hs t).congr ?_
  filter_upwards [Iio_mem_nhds hT] with u hu
  exact (hEq u hu).symm
