-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiAtZeroEqualsInitialAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:22:12.057858+00:00
-- url     : https://prove2.me/submissions/bfa248c7-93d1-43d8-8a88-6f044d3a83ea

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonRightContinuousAE
import Theorems.Thm_Kyprianou_Ch01_reverseCompoundPoissonIntegerStartsAtInitialStateAE
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiZeroTimePathwiseOfContinuousAtZero
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
    ∀ y : ℕ, ∀ᵐ ω ∂Q,
      (compoundPoissonToBranching
        (integerCompoundPoisson y arrival marks) 0 ω).toNat = y := by
  intro y
  have hRC :=
    Kyprianou.Ch01.integerCompoundPoissonRightContinuousAE
      Q rate hrate arrival marks jumpLaw hdriver y
  have hStart :=
    Kyprianou.Ch01.reverseCompoundPoissonIntegerStartsAtInitialStateAE
      Q rate hrate arrival marks jumpLaw hdriver y
  filter_upwards [hRC, hStart] with ω hrc h0
  have hn : 0 ≤ integerCompoundPoisson y arrival marks 0 ω := by
    rw [h0]
    exact Int.natCast_nonneg y
  have hRecover :=
    Kyprianou.Ch01.reverseLampertiZeroTimePathwiseOfContinuousAtZero
      (integerCompoundPoisson y arrival marks) ω hn (hrc 0)
  simpa [h0] using hRecover
