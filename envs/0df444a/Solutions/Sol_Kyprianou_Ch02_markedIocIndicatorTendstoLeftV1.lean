-- Prove2me | solution 1 for Kyprianou.Ch02.markedIocIndicatorTendstoLeftV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:58:00.037867+00:00
-- url     : https://prove2.me/submissions/0e6a0540-4aef-4239-baf1-0205f107bf02

import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (A : Set ℝ) (t : ℝ≥0) (z : ℝ × ℝ) :
    Tendsto (fun s : ℝ≥0 => (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ A).indicator Prod.snd z)
      (nhdsWithin t (Set.Iio t))
      (nhds ((Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ A).indicator Prod.snd z)) := by
  let L : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ A
  have hstay : ∀ᶠ s in nhdsWithin t (Set.Iio t), s < t := self_mem_nhdsWithin
  have hcoe : Tendsto (fun s : ℝ≥0 => (s : ℝ))
      (nhdsWithin t (Set.Iio t)) (nhds (t : ℝ)) :=
    NNReal.continuous_coe.continuousWithinAt
  apply tendsto_nhds_of_eventually_eq
  by_cases hz : z ∈ L
  · have hlt : z.1 < (t : ℝ) := hz.1.2
    filter_upwards [hcoe.eventually (Ioi_mem_nhds hlt)] with s hs
    have hz' : z ∈ Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ A :=
      ⟨⟨hz.1.1, (show z.1 < (s : ℝ) from hs).le⟩, hz.2⟩
    simp [Set.indicator_of_mem hz', show z ∈ Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ A from hz]
  · filter_upwards [hstay] with s hs
    have hz' : z ∉ Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ A := by
      intro h
      exact hz ⟨⟨h.1.1, lt_of_le_of_lt h.1.2 (by exact_mod_cast hs)⟩, h.2⟩
    simp [Set.indicator_of_notMem hz', show z ∉ Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ A from hz]
