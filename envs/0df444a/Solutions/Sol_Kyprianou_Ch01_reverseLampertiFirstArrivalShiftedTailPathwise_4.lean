-- Prove2me | solution 4 for Kyprianou.Ch01.reverseLampertiFirstArrivalShiftedTailPathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:26:54.590077+00:00
-- url     : https://prove2.me/submissions/b496c9bd-5d71-4178-acd4-9fd3e7f47714

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonDriverArrivalStrictMonoDivergesPublic
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstArrivalPositiveFromSurvivalAE
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstMarkOffspringSupportAE
import Theorems.Thm_Kyprianou_Ch01_reverseIntegerCompoundPoissonConstantBeforeFirstArrival
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonShiftAfterFirstMark
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiShiftedPathClockNonnegativeStart
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonDriverShiftedTail
import Theorems.Thm_Kyprianou_Ch01_reverseCompoundPoissonIntegerStartsAtInitialStateAE
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
    ∀ᵐ ω ∂Q, ¬ ((y : ℝ) * (t : ℝ) <
          ProbabilityTheory.arrival arrival 0 ω) →
      (compoundPoissonToBranching
            (integerCompoundPoisson y arrival marks) t ω).toNat =
      (compoundPoissonToBranching
            (integerCompoundPoisson
              ((y - 1) +
                (Int.floor (marks 0 ω + 1)).toNat)
              (fun n w => arrival (n + 1) w)
              (fun n w => marks (n + 1) w))
            (Real.toNNReal
              ((t : ℝ) -
                ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
            ω).toNat := by
  obtain ⟨hMonoAE, hTopAE⟩ :=
    Kyprianou.Ch01.compoundPoissonDriverArrivalStrictMonoDivergesPublic
      Q rate hrate arrival marks jumpLaw hdriver
  have hPosAE : ∀ᵐ w ∂Q,
      0 < ProbabilityTheory.arrival arrival 0 w :=
    Kyprianou.Ch01.compoundPoissonFirstArrivalPositiveFromSurvivalAE
      Q rate hrate arrival marks jumpLaw hdriver
  have hMarkAE : ∀ᵐ w ∂Q, ∃ j : ℕ,
      marks 0 w = (j : ℝ) - 1 :=
    Kyprianou.Ch01.compoundPoissonFirstMarkOffspringSupportAE
      Q rate hrate arrival marks jumpLaw hdriver hSupport
  have hTailDriver : IsCompoundPoissonDriver
      (fun n w => arrival (n + 1) w)
      (fun n w => marks (n + 1) w) rate jumpLaw Q :=
    Kyprianou.Ch01.compoundPoissonDriverShiftedTail
      Q rate arrival marks jumpLaw hdriver
  have hTailStarts : ∀ᵐ w ∂Q, ∀ z : ℕ,
      integerCompoundPoisson z
        (fun n w => arrival (n + 1) w)
        (fun n w => marks (n + 1) w) 0 w = (z : ℤ) := by
    rw [MeasureTheory.ae_all_iff]
    exact Kyprianou.Ch01.reverseCompoundPoissonIntegerStartsAtInitialStateAE
      Q rate hrate (fun n w => arrival (n + 1) w)
      (fun n w => marks (n + 1) w) jumpLaw hTailDriver
  filter_upwards [hMonoAE, hTopAE, hPosAE, hMarkAE, hTailStarts]
    with w hMono hTop hPos hMark hStart
  intro hFirst
  obtain ⟨j, hj⟩ := hMark
  let X : ℝ≥0 → Ω → ℤ :=
    integerCompoundPoisson y arrival marks
  let Y : ℝ≥0 → Ω → ℤ :=
    integerCompoundPoisson ((y - 1) + j)
      (fun n z => arrival (n + 1) z)
      (fun n z => marks (n + 1) z)
  have hPrefix (u : ℝ≥0)
      (hu : (u : ℝ) < ProbabilityTheory.arrival arrival 0 w) :
      X u w = (y : ℤ) :=
    Kyprianou.Ch01.reverseIntegerCompoundPoissonConstantBeforeFirstArrival
      y arrival marks u w hu
  have hSuffix (u : ℝ≥0)
      (hu : ProbabilityTheory.arrival arrival 0 w ≤ (u : ℝ)) :
      X u w =
        Y (Real.toNNReal ((u : ℝ) -
          ProbabilityTheory.arrival arrival 0 w)) w :=
    Kyprianou.Ch01.integerCompoundPoissonShiftAfterFirstMark
      y j arrival marks w hy hMono hTop hj u hu
  have hTailNonneg : (0 : ℤ) ≤ Y 0 w := by
    change (0 : ℤ) ≤ integerCompoundPoisson ((y - 1) + j)
      (fun n z => arrival (n + 1) z)
      (fun n z => marks (n + 1) z) 0 w
    rw [hStart ((y - 1) + j)]
    exact_mod_cast Nat.zero_le ((y - 1) + j)
  have hClock :=
    Kyprianou.Ch01.reverseLampertiShiftedPathClockNonnegativeStart
      X Y w y hy t (ProbabilityTheory.arrival arrival 0 w)
      hPos.le (le_of_not_gt hFirst) hPrefix hSuffix hTailNonneg
  have hMarkNat : (Int.floor (marks 0 w + 1)).toNat = j := by
    have hm : marks 0 w + 1 = (j : ℝ) := by
      rw [hj]
      ring
    rw [hm]
    norm_num
  simpa only [X, Y, hMarkNat] using hClock
