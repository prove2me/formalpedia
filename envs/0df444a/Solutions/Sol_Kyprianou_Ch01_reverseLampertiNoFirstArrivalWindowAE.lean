-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNoFirstArrivalWindowAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:31:18.692422+00:00
-- url     : https://prove2.me/submissions/c240ea6d-1b16-49fc-9af7-fc8110ca8861

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiAtZeroEqualsInitialAE
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiPositiveTimeNoFirstArrivalWindowAE
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ (y : ℕ) (t : ℝ≥0), ∀ᵐ ω ∂Q,
      (y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω →
      (compoundPoissonToBranching
      (integerCompoundPoisson y arrival marks) t ω).toNat = y := by
  intro y t
  by_cases hZero : t = 0
  · subst t
    have hz :=
      Kyprianou.Ch01.reverseLampertiAtZeroEqualsInitialAE
        Q rate hrate arrival marks jumpLaw hdriver y
    filter_upwards [hz] with ω hPopulation hBefore
    simpa using hPopulation
  · have htPos : 0 < t := (pos_iff_ne_zero).2 hZero
    exact Kyprianou.Ch01.reverseLampertiPositiveTimeNoFirstArrivalWindowAE
      Q rate hrate arrival marks jumpLaw hdriver y t htPos
