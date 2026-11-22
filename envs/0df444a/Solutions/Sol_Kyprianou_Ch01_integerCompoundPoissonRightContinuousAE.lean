-- Prove2me | solution 1 for Kyprianou.Ch01.integerCompoundPoissonRightContinuousAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:44:17.424246+00:00
-- url     : https://prove2.me/submissions/c4a0bf69-7094-45cd-bb25-da3e140a7825

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonDriverArrivalStrictMonoDivergesPublic
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonRightContinuousOfRegularArrivals
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Source all-time right-continuity follows from a common conull event of
arrival regularity and the deterministic zero-drift lattice-path lemma. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ y : ℕ, ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun s : ℝ≥0 => integerCompoundPoisson y arrival marks s ω)
        (Set.Ici t) t := by
  obtain ⟨hMonoAE, hTopAE⟩ :=
    Kyprianou.Ch01.compoundPoissonDriverArrivalStrictMonoDivergesPublic
      Q rate hRate arrival marks jumpLaw hDriver
  intro y
  filter_upwards [hMonoAE, hTopAE] with ω hmono htop
  intro t
  change ContinuousWithinAt
    (fun s : ℝ≥0 =>
      Int.floor ((y : ℝ) +
        ProbabilityTheory.piecewisePath 0 0
          (fun n => ProbabilityTheory.arrival arrival n ω)
          (fun n => marks n ω) (s : ℝ)))
    (Set.Ici t) t
  exact Kyprianou.Ch01.integerCompoundPoissonRightContinuousOfRegularArrivals
    y (fun n => ProbabilityTheory.arrival arrival n ω)
    (fun n => marks n ω) hmono htop t
