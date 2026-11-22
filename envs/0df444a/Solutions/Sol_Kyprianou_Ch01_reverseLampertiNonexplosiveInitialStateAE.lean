-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveInitialStateAE
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:41:44.539207+00:00
-- url     : https://prove2.me/submissions/37353768-9ba3-4276-9bf4-c0f0bd8135bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseCompoundPoissonIntegerStartsAtInitialStateAE
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonRightContinuousAE
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiZeroTimePathwiseOfContinuousAtZero
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω) :
    ∀ y : ℕ, ∀ᵐ ω ∂Q,
      (compoundPoissonToBranching
        (integerCompoundPoisson y arrival marks) 0 ω).toNat = y := by
  intro y
  have hStart :=
    Kyprianou.Ch01.reverseCompoundPoissonIntegerStartsAtInitialStateAE
      Q rate hrate arrival marks jumpLaw hdriver y
  have hRight :=
    Kyprianou.Ch01.integerCompoundPoissonRightContinuousAE
      Q rate hrate arrival marks jumpLaw hdriver y
  filter_upwards [hStart, hRight] with ω hInitial hContinuous
  have hNonneg : 0 ≤ integerCompoundPoisson y arrival marks 0 ω := by
    simp [hInitial]
  have hZero :=
    Kyprianou.Ch01.reverseLampertiZeroTimePathwiseOfContinuousAtZero
      (integerCompoundPoisson y arrival marks) ω hNonneg (hContinuous 0)
  simpa [hInitial] using hZero
