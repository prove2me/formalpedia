-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiFirstArrivalMarkedRestartClock
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:31:36.241425+00:00
-- url     : https://prove2.me/submissions/66aeb74a-fca3-4a2c-96b1-fe918548e5d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstHoldingMarkProductLaw
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonDriverShiftedTail
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstPairIndependentOfShiftedTail
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonDriverJointInfinitePiLaw
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalIndependentProductIntegration
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
    (Q (⋃ j : ℕ, {ω |
          marks 0 ω = (j : ℝ) - 1 ∧
          (compoundPoissonToBranching
            (integerCompoundPoisson
              ((y - 1) + j)
              (fun n w => arrival (n + 1) w)
              (fun n w => marks (n + 1) w))
            (Real.toNNReal
              ((t : ℝ) -
                ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
            ω).toNat = k ∧
          ¬ ((y : ℝ) * (t : ℝ) <
            ProbabilityTheory.arrival arrival 0 ω)})).toReal =
        ∫ a in (0 : ℝ)..(y : ℝ) * (t : ℝ),
          (rate : ℝ) * Real.exp (-((rate : ℝ) * a)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j)
                (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal := by
  have hHeadLaw :=
    Kyprianou.Ch01.compoundPoissonFirstHoldingMarkProductLaw
      Q rate arrival marks jumpLaw hdriver
  have hTailDriver :=
    Kyprianou.Ch01.compoundPoissonDriverShiftedTail
      Q rate arrival marks jumpLaw hdriver
  have hTailIndep :=
    Kyprianou.Ch01.compoundPoissonFirstPairIndependentOfShiftedTail
      Q rate arrival marks jumpLaw hdriver
  have hJoint :=
    Kyprianou.Ch01.compoundPoissonDriverJointInfinitePiLaw
      Q rate arrival marks jumpLaw hdriver
  exact Kyprianou.Ch01.reverseLampertiFirstArrivalIndependentProductIntegration
    Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
    hdriver hSupport hJumpMass hNoExplosion K hRealisation
    hHeadLaw hTailDriver hTailIndep hJoint y hy t ht k

