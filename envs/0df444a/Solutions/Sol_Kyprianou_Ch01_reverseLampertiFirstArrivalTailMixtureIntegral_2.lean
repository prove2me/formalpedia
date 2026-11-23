-- Prove2me | solution 2 for Kyprianou.Ch01.reverseLampertiFirstArrivalTailMixtureIntegral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:02:56.453697+00:00
-- url     : https://prove2.me/submissions/813983e3-e7e6-4b9b-82c6-f7d428f012c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_measureFirstMarkUnionEqFloorFromAESupport
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstMarkOffspringSupportAE
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalMarkedRestartClock
import Theorems.Thm_Kyprianou_Ch01_realScaledIntervalIntegral
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
    (Q { ω |
          (compoundPoissonToBranching
            (integerCompoundPoisson
              ((y - 1) +
                (Int.floor (marks 0 ω + 1)).toNat)
              (fun n w => arrival (n + 1) w)
              (fun n w => marks (n + 1) w))
            (Real.toNNReal
              ((t : ℝ) -
                ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
            ω).toNat = k ∧
          ¬ ((y : ℝ) * (t : ℝ) <
          ProbabilityTheory.arrival arrival 0 ω) }).toReal =
        ∫ s in (0 : ℝ)..(t : ℝ),
          ((rate : ℝ) * (y : ℝ)) * Real.exp (-(((rate : ℝ) * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal := by
  have hSupportAE :=
    Kyprianou.Ch01.compoundPoissonFirstMarkOffspringSupportAE
      Q rate hrate arrival marks jumpLaw hdriver hSupport
  have hUnion :=
    Kyprianou.Ch01.measureFirstMarkUnionEqFloorFromAESupport
      Q (fun w => marks 0 w) hSupportAE
      (fun j w =>
        (compoundPoissonToBranching
          (integerCompoundPoisson ((y - 1) + j)
            (fun n w' => arrival (n + 1) w')
            (fun n w' => marks (n + 1) w'))
          (Real.toNNReal ((t : ℝ) -
            ProbabilityTheory.arrival arrival 0 w / (y : ℝ))) w).toNat)
      (fun w => ¬ ((y : ℝ) * (t : ℝ) <
        ProbabilityTheory.arrival arrival 0 w)) k
  have hRestart :=
    Kyprianou.Ch01.reverseLampertiFirstArrivalMarkedRestartClock
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion K hRealisation
      y hy t ht k
  let f : ℝ → ℝ := fun a =>
    (rate : ℝ) * Real.exp (-((rate : ℝ) * a)) *
      ∑' j : ℕ, (offspring j).toReal *
        (K ((y - 1) + j)
          (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal
  have hScale :=
    Kyprianou.Ch01.realScaledIntervalIntegral (y : ℝ) (t : ℝ) f
  have hPoint (s : ℝ) :
      (y : ℝ) * f ((y : ℝ) * s) =
        ((rate : ℝ) * (y : ℝ)) *
          Real.exp (-(((rate : ℝ) * (y : ℝ)) * s)) *
          ∑' j : ℕ, (offspring j).toReal *
            (K ((y - 1) + j)
              (Real.toNNReal ((t : ℝ) - s)) k).toReal := by
    have hy0 : (y : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hy)
    have hDiv : ((y : ℝ) * s) / (y : ℝ) = s := by
      field_simp [hy0]
    have hExp :
        -((rate : ℝ) * ((y : ℝ) * s)) =
          -(((rate : ℝ) * (y : ℝ)) * s) := by ring
    dsimp [f]
    rw [hDiv, hExp]
    ring
  have hTime :
      (∫ a in (0 : ℝ)..(y : ℝ) * (t : ℝ), f a) =
        ∫ s in (0 : ℝ)..(t : ℝ),
          ((rate : ℝ) * (y : ℝ)) *
            Real.exp (-(((rate : ℝ) * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j)
                (Real.toNNReal ((t : ℝ) - s)) k).toReal := by
    rw [← hScale]
    exact intervalIntegral.integral_congr (by
      intro s hs
      exact hPoint s)
  rw [← hUnion]
  exact hRestart.trans hTime
