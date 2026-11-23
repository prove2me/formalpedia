-- Prove2me | solution 2 for Kyprianou.Ch01.reverseLampertiNonexplosiveDiagonalGenerator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:16:38.931521+00:00
-- url     : https://prove2.me/submissions/ea7d0c72-b51f-4fa5-8cff-dbd44282a470

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiZeroBranchingTimeAbsorbed
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosivePositiveDiagonalGenerator
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
          (integerCompoundPoisson y arrival marks) t ω).toNat = k}) :
    ∀ y : ℕ,
      HasDerivWithinAt
        (fun t : ℝ => ((K y (Real.toNNReal t)) y).toReal)
        (-((rate : ℝ) * (y : ℝ)))
        (Set.Ici 0) 0 := by
  intro y
  by_cases hy : y = 0
  · subst y
    have hZero :=
      Kyprianou.Ch01.reverseLampertiZeroBranchingTimeAbsorbed
        Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
        hdriver hSupport hJumpMass hNoExplosion K hRealisation
    have hconst :
        (fun t : ℝ => ((K 0 (Real.toNNReal t)) 0).toReal) =
        (fun _ : ℝ => (1 : ℝ)) := by
      funext t
      rw [hZero (Real.toNNReal t) 0]
      simp
    simpa only [Nat.cast_zero, mul_zero, neg_zero, hconst] using
      (hasDerivWithinAt_const (0 : ℝ) (Set.Ici 0) (1 : ℝ))
  · exact
      Kyprianou.Ch01.reverseLampertiNonexplosivePositiveDiagonalGenerator
        Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
        hdriver hSupport hJumpMass hNoExplosion K hRealisation y
        (Nat.pos_of_ne_zero hy)
