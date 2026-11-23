-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiFirstArrivalOneOffspringClock
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T18:47:06.390997+00:00
-- url     : https://prove2.me/submissions/4b54b5e9-f923-4cf7-894a-31d75466c18c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstHoldingMarkProductLaw
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonDriverShiftedTail
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstPairIndependentOfShiftedTail
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonDriverJointInfinitePiLaw
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalOneOffspringFromHeadTail

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal Interval
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
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k j : ℕ) :
    (Q {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal
            ((t : ℝ) - ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        ¬ ((y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω)}).toReal =
      ∫ a in (0 : ℝ)..(y : ℝ) * (t : ℝ),
        (rate : ℝ) * Real.exp (-((rate : ℝ) * a)) * (offspring j).toReal *
          (K ((y - 1) + j)
            (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal := by
  have hHead :=
    compoundPoissonFirstHoldingMarkProductLaw Q rate arrival marks jumpLaw hdriver
  have hTail :=
    compoundPoissonDriverShiftedTail Q rate arrival marks jumpLaw hdriver
  have hInd :=
    compoundPoissonFirstPairIndependentOfShiftedTail Q rate arrival marks jumpLaw hdriver
  have hPi :=
    compoundPoissonDriverJointInfinitePiLaw Q rate arrival marks jumpLaw hdriver
  exact reverseLampertiFirstArrivalOneOffspringFromHeadTail Q rate hrate offspring hNoZeroJumps
    arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion K hRealisation
    hHead hTail hInd hPi y hy t ht k j
