-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiFirstArrivalPoissonClockMixture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T17:52:34.921826+00:00
-- url     : https://prove2.me/submissions/a0bb5f37-ea18-4ea3-a3e9-f4c25a1027a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstMarkOffspringSupportAE
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalMarkedRestartClock

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
        ∫ a in (0 : ℝ)..(y : ℝ) * (t : ℝ),
          (rate : ℝ) * Real.exp (-((rate : ℝ) * a)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j)
                (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal := by
  let marked : Set Ω :=
    ⋃ j : ℕ, {ω |
      marks 0 ω = (j : ℝ) - 1 ∧
      (compoundPoissonToBranching
        (integerCompoundPoisson
          ((y - 1) + j)
          (fun n w => arrival (n + 1) w)
          (fun n w => marks (n + 1) w))
        (Real.toNNReal
          ((t : ℝ) - ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
        ω).toNat = k ∧
      ¬ ((y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω)}
  have hSupportAE :=
    compoundPoissonFirstMarkOffspringSupportAE Q rate hrate arrival marks jumpLaw
      hdriver hSupport
  have hFloor : ∀ {j : ℕ} {ω : Ω}, marks 0 ω = (j : ℝ) - 1 →
      (Int.floor (marks 0 ω + 1)).toNat = j := by
    intro j ω hj
    rw [hj]
    have : (j : ℝ) - 1 + 1 = (j : ℝ) := by ring
    rw [this, Int.floor_natCast, Int.toNat_natCast]
  have hSet :
      {ω |
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + (Int.floor (marks 0 ω + 1)).toNat)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal
            ((t : ℝ) - ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        ¬ ((y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω)}
        =ᵐ[Q] marked := by
    filter_upwards [hSupportAE] with ω ⟨j, hj⟩
    refine propext ?_
    constructor
    · intro hω
      have hH : (Int.floor (marks 0 ω + 1)).toNat = j := hFloor hj
      refine mem_iUnion.mpr ⟨j, hj, ?_, hω.2⟩
      rw [← hH]
      exact hω.1
    · intro hω
      rcases mem_iUnion.mp hω with ⟨j', hjmark, hpop, hearly⟩
      have hH : (Int.floor (marks 0 ω + 1)).toNat = j' := hFloor hjmark
      refine ⟨?_, hearly⟩
      rw [hH]
      exact hpop
  have hQ := measure_congr hSet
  rw [hQ]
  simpa [marked] using
    reverseLampertiFirstArrivalMarkedRestartClock Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion K hRealisation
      y hy t ht k
