-- Prove2me | solution 1 for Kyprianou.Ch01.integerCompoundPoissonLinearGrowthFromReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:55:26.333195+00:00
-- url     : https://prove2.me/submissions/734ea15e-3302-493e-a37a-5d7cc9fbc2b7

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Floor of a linearly upper-bounded compound Poisson path is linearly bounded. -/
theorem solution
    {Ω : Type*} (y : ℕ) (arrival marks : ℕ → Ω → ℝ)
    (ω : Ω) (K : ℝ) (hK : 0 ≤ K)
    (hGrowth : ∀ t : ℝ≥0,
      ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω ≤
        K * (1 + (t : ℝ))) :
    ∀ t : ℝ≥0,
      (integerCompoundPoisson y arrival marks t ω : ℝ) ≤
        ((y : ℝ) + K + 1) * (1 + (t : ℝ)) := by
  intro t
  have ht : (0 : ℝ) ≤ (t : ℝ) := NNReal.coe_nonneg t
  have hy : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have hfloor : ((Int.floor ((y : ℝ) +
      ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω) : ℤ) : ℝ) ≤
        (y : ℝ) +
          ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω :=
    Int.floor_le _
  change ((Int.floor ((y : ℝ) +
    ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω) : ℤ) : ℝ) ≤
        ((y : ℝ) + K + 1) * (1 + (t : ℝ))
  have hpos : 0 ≤ (y : ℝ) * (t : ℝ) := mul_nonneg hy ht
  nlinarith [hGrowth t]
