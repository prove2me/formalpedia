-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveInitialAtoms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:50:51.105797+00:00
-- url     : https://prove2.me/submissions/ad1bcec8-7eae-4215-9032-c490782920d4

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveInitialStateAE
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
    ∀ (y k : ℕ),
      Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) 0 ω).toNat = k} =
        (PMF.pure y) k := by
  intro y k
  have hzero :=
    Kyprianou.Ch01.reverseLampertiNonexplosiveInitialStateAE
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion y
  have hevent :
      Q {ω : Ω | (compoundPoissonToBranching
        (integerCompoundPoisson y arrival marks) 0 ω).toNat = k} =
      Q {ω : Ω | y = k} := by
    apply MeasureTheory.measure_congr
    filter_upwards [hzero] with ω hω
    change ((compoundPoissonToBranching
      (integerCompoundPoisson y arrival marks) 0 ω).toNat = k) = (y = k)
    rw [hω]
  rw [hevent]
  by_cases hyk : y = k
  · subst k
    simp
  · have hky : k ≠ y := Ne.symm hyk
    simp [hyk, hky]
