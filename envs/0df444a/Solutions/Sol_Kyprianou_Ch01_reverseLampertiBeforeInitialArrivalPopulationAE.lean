-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiBeforeInitialArrivalPopulationAE
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:06:02.6038+00:00
-- url     : https://prove2.me/submissions/1b093b52-8049-4e2a-90f1-822d724360f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiConstantPrefixFromOccupationWitness
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiBeforeFirstArrivalOccupationWitness
import Theorems.Thm_Kyprianou_Ch01_reverseIntegerCompoundPoissonConstantBeforeFirstArrival
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
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (y : ℕ) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q,
      ((y : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 ω) →
      (compoundPoissonToBranching
        (integerCompoundPoisson y arrival marks) t ω).toNat = y := by
  have hForall (omega : Ω) :
      ((y : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 omega) ->
      (compoundPoissonToBranching
        (integerCompoundPoisson y arrival marks) t omega).toNat = y := by
    intro hBefore
    have hConst : ∀ s : NNReal,
        (s : Real) < ProbabilityTheory.arrival arrival 0 omega ->
        integerCompoundPoisson y arrival marks s omega = (y : Int) := by
      intro s hs
      exact Kyprianou.Ch01.reverseIntegerCompoundPoissonConstantBeforeFirstArrival
        y arrival marks s omega hs
    have hWitness :=
      Kyprianou.Ch01.reverseLampertiBeforeFirstArrivalOccupationWitness
        y arrival marks t omega hBefore
    exact Kyprianou.Ch01.reverseLampertiConstantPrefixFromOccupationWitness
      (integerCompoundPoisson y arrival marks) omega y t
      (ProbabilityTheory.arrival arrival 0 omega) hConst hWitness
  exact Filter.Eventually.of_forall hForall