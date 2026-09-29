-- Prove2me | solution 1 for MarkovChainCLT.coord_future_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:47:46.525527+00:00
-- url     : https://prove2.me/submissions/8259ae7f-aa3d-496c-80fd-6b37b05f2ac2

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (Y : ℕ → Ω → E) (m : ℕ) :
    Measurable[processSigma Y (Set.Ici m)] (Y m) := by
  refine (measurable_iff_comap_le.2 le_rfl).mono ?_ le_rfl
  refine le_iSup₂ (f := fun i (_ : i ∈ Set.Ici m) =>
    MeasurableSpace.comap (Y i) inferInstance) m ?_
  simp
