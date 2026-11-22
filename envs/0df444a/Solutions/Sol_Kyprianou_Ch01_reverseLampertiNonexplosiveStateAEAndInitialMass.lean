-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveStateAEAndInitialMass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:53:56.551674+00:00
-- url     : https://prove2.me/submissions/92ae6330-35eb-4404-b34c-459ada5a57b3

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveStateAEMeasurable
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveInitialAtoms
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
    (∀ (y : ℕ) (t : ℝ≥0),
      AEMeasurable
        (fun ω : Ω => (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat) Q) ∧
    (∀ (y k : ℕ),
      Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) 0 ω).toNat = k} =
        (PMF.pure y) k) := by
  constructor
  · exact Kyprianou.Ch01.reverseLampertiNonexplosiveStateAEMeasurable
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion
  · exact Kyprianou.Ch01.reverseLampertiNonexplosiveInitialAtoms
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion
