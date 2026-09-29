-- Prove2me | solution 1 for MarkovChainCLT.coord_past_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:47:45.981745+00:00
-- url     : https://prove2.me/submissions/14e3bc10-8c21-413a-8cf2-a1225ae781c2

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (Y : ℕ → Ω → E) (k : ℕ) :
    Measurable[processSigma Y (Set.Iic k)] (Y k) := by
  refine (measurable_iff_comap_le.2 le_rfl).mono ?_ le_rfl
  exact le_iSup₂ (f := fun i (_ : i ∈ Set.Iic k) =>
    MeasurableSpace.comap (Y i) inferInstance) k (Set.mem_Iic.2 le_rfl)
