-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNoJumpStateRemainsInitial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:44:31.493975+00:00
-- url     : https://prove2.me/submissions/19767a0b-2fae-4f43-a8fc-69d4e8c490e2

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNoArrivalOnePopulationIndicator
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
    (K : PopulationLaws)
    (hRealisation : ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k})
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k : ℕ) :
    Q {ω |
        (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k ∧
        (y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω} =
      if k = y then
        Q {ω | (y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω}
      else 0 := by
  convert
    (Kyprianou.Ch01.reverseLampertiNoArrivalOnePopulationIndicator
      Q rate hrate offspring hNoZeroJumps arrival marks
      jumpLaw hdriver hSupport hJumpMass hNoExplosion y t k)
    using 1
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, and_comm]

