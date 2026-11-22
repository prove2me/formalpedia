-- Prove2me | solution 1 for Kyprianou.Ch01.firstNonpositiveLatticeAEMeasurableFromDriver
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:41:09.199534+00:00
-- url     : https://prove2.me/submissions/9f3eec22-b84d-491d-9cda-24b27f965c22

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonFixedTimeMeasurable
import Theorems.Thm_Kyprianou_Ch01_rationalFirstNonpositiveLatticeClockMeasurable
import Theorems.Thm_Kyprianou_Ch01_firstNonpositiveLatticeEqRationalOfRightContinuous
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonRightContinuousAE
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Source first-nonpositive clock is a.e. equal to an explicitly measurable
rational first-hit clock, once the lattice driver is a.e. right-continuous. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ y : ℕ,
      AEMeasurable
        (fun ω : Ω =>
          firstNonpositiveLattice
            (integerCompoundPoisson y arrival marks) ω) Q := by
  intro y
  let X : ℝ≥0 → Ω → ℤ := integerCompoundPoisson y arrival marks
  let C : Ω → WithTop ℝ≥0 := fun ω =>
    ⨅ r : ℚ,
      if X (Real.toNNReal (r : ℝ)) ω ≤ 0 then
        ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
      else ⊤
  have hXm : ∀ t : ℝ≥0, Measurable (X t) := by
    intro t
    exact Kyprianou.Ch01.integerCompoundPoissonFixedTimeMeasurable
      y arrival marks hDriver.measurable_interarrival
      hDriver.measurable_mark t
  have hCm : Measurable C :=
    Kyprianou.Ch01.rationalFirstNonpositiveLatticeClockMeasurable
      X hXm
  have hRight : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => X s ω) (Ici t) t :=
    Kyprianou.Ch01.integerCompoundPoissonRightContinuousAE
      Q rate hRate arrival marks jumpLaw hDriver y
  apply AEMeasurable.congr hCm.aemeasurable
  filter_upwards [hRight] with ω hω
  exact (Kyprianou.Ch01.firstNonpositiveLatticeEqRationalOfRightContinuous
    X ω hω).symm
