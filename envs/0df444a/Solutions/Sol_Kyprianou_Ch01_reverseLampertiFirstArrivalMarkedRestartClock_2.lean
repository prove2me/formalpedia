-- Prove2me | solution 2 for Kyprianou.Ch01.reverseLampertiFirstArrivalMarkedRestartClock
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T18:39:50.872037+00:00
-- url     : https://prove2.me/submissions/0f8bb4b2-491c-4293-b8b7-ed21d690268c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_reverseLampertiMarkedRestartNullMeasurable
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalOneOffspringClock
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiOffspringKernelIntervalSum

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
  let F : ℕ → Set Ω := fun j => {ω |
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
  have hdisj : Pairwise (fun i j => Disjoint (F i) (F j)) := by
    intro i j hij
    refine disjoint_left.mpr ?_
    intro ω hi hj
    apply hij
    have hmark : (i : ℝ) - 1 = (j : ℝ) - 1 := by rw [← hi.1, hj.1]
    exact Nat.cast_injective ((sub_left_inj).mp hmark)
  have hnull : ∀ j, NullMeasurableSet (F j) Q := by
    intro j
    simpa [F] using reverseLampertiMarkedRestartNullMeasurable Q arrival marks y t k j
  have hsum : Q (⋃ j, F j) = ∑' j, Q (F j) :=
    measure_iUnion₀ (fun i j hij => (hdisj hij).aedisjoint) hnull
  have htop : ∀ j, Q (F j) ≠ ∞ := fun j => measure_ne_top Q (F j)
  rw [show (⋃ j : ℕ, {ω |
      marks 0 ω = (j : ℝ) - 1 ∧
      (compoundPoissonToBranching
        (integerCompoundPoisson
          ((y - 1) + j)
          (fun n w => arrival (n + 1) w)
          (fun n w => marks (n + 1) w))
        (Real.toNNReal
          ((t : ℝ) - ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
        ω).toNat = k ∧
      ¬ ((y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω)}) = ⋃ j, F j
    by rfl]
  rw [hsum, ENNReal.tsum_toReal_eq htop]
  have hpiece : ∀ j, (Q (F j)).toReal =
      ∫ a in (0 : ℝ)..(y : ℝ) * (t : ℝ),
        (rate : ℝ) * Real.exp (-((rate : ℝ) * a)) * (offspring j).toReal *
          (K ((y - 1) + j)
            (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal := by
    intro j
    simpa [F] using
      reverseLampertiFirstArrivalOneOffspringClock Q rate hrate offspring hNoZeroJumps
        arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion K hRealisation
        y hy t ht k j
  simp_rw [hpiece]
  exact reverseLampertiOffspringKernelIntervalSum rate offspring K y t k
