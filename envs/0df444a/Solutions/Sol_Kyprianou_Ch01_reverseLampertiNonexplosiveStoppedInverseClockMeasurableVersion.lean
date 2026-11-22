-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveStoppedInverseClockMeasurableVersion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:56:23.148462+00:00
-- url     : https://prove2.me/submissions/c27b9d45-466f-43ce-adcf-f9368d7f292f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveInverseReciprocalClockVersion
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveFirstNegativePassageVersion
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The stopped clock is the pointwise minimum of two measurable clock
versions that agree simultaneously on a common full-measure event. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω) :
    ∀ y : ℕ, ∃ T : ℝ≥0 → Ω → WithTop ℝ≥0,
      (∀ t : ℝ≥0, Measurable (T t)) ∧
      ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
        T t ω =
          min (inverseReciprocalOccupation
            (integerCompoundPoisson y arrival marks) t ω)
            (firstNegativePassage
              (integerCompoundPoisson y arrival marks) ω) := by
  intro y
  obtain ⟨U, hU, hUEq⟩ :=
    Kyprianou.Ch01.reverseLampertiNonexplosiveInverseReciprocalClockVersion
      Q rate hrate arrival marks jumpLaw hdriver hNoExplosion y
  obtain ⟨V, hV, hVEq⟩ :=
    Kyprianou.Ch01.reverseLampertiNonexplosiveFirstNegativePassageVersion
      Q rate hrate arrival marks jumpLaw hdriver y
  let T : ℝ≥0 → Ω → WithTop ℝ≥0 := fun t ω => min (U t ω) (V ω)
  refine ⟨T, ?_, ?_⟩
  · intro t
    exact (hU t).min hV
  · filter_upwards [hUEq, hVEq] with ω hu hv
    intro t
    simp only [T, hu t, hv]
