-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiFirstJumpRestartIntegral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:55:56.702001+00:00
-- url     : https://prove2.me/submissions/829f2304-1434-47ad-9285-4b5c66c97a0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstJumpRestartKernelIntegrable
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstJumpRestartKernelIdentity
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators Interval
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
    IntervalIntegrable
        (fun s : ℝ =>
          ((rate : ℝ) * (y : ℝ)) * Real.exp (-(((rate : ℝ) * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal)
        volume 0 (t : ℝ) ∧
      (Q {ω |
          (compoundPoissonToBranching
            (integerCompoundPoisson y arrival marks) t ω).toNat = k ∧
          ¬ ((y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω)}).toReal =
        ∫ s in (0 : ℝ)..(t : ℝ),
          ((rate : ℝ) * (y : ℝ)) * Real.exp (-(((rate : ℝ) * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal := by
  constructor
  · exact Kyprianou.Ch01.reverseLampertiFirstJumpRestartKernelIntegrable
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion K hRealisation y hy t ht k
  · exact Kyprianou.Ch01.reverseLampertiFirstJumpRestartKernelIdentity
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion K hRealisation y hy t ht k

