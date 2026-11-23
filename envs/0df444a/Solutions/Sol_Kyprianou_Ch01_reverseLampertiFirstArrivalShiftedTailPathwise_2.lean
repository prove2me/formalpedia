-- Prove2me | solution 2 for Kyprianou.Ch01.reverseLampertiFirstArrivalShiftedTailPathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:10:29.789311+00:00
-- url     : https://prove2.me/submissions/449344b0-448e-4045-a142-a2284ba6ece2

import Theorems.Thm_ProbabilityTheory_lt_jumpCount_iff
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_strictMono_arrival
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_tendsto_arrival
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
import Theorems.Thm_Kyprianou_Ch01_reverseIntegerCompoundPoissonConstantBeforeFirstArrival
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstMarkOffspringSupportAE
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiShiftedPathClockNonnegativeStart
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonShiftAfterFirstMark

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Finset
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
set_option linter.unusedVariables false


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
  have hMonoAE := IsCompoundPoissonDriver.ae_strictMono_arrival hdriver hrate
  have hTopAE := IsCompoundPoissonDriver.ae_tendsto_arrival hdriver hrate
  have hPosAE := IsCompoundPoissonDriver.ae_interarrival_pos hdriver hrate
  have hMarkAE :=
    compoundPoissonFirstMarkOffspringSupportAE Q rate hrate arrival marks jumpLaw
      hdriver hSupport
  filter_upwards [hMonoAE, hTopAE, hPosAE, hMarkAE] with ω hMono hTop hPos hMark hJump
  rcases hMark with ⟨j, hj⟩
  set A : ℝ := ProbabilityTheory.arrival arrival 0 ω
  have hA0 : 0 < A := by
    have h0 : A = arrival 0 ω := by
      simp [A, ProbabilityTheory.arrival]
    rw [h0]
    exact hPos 0
  have hFirst : A ≤ (y : ℝ) * (t : ℝ) := not_lt.mp hJump
  have hFloor : (Int.floor (marks 0 ω + 1)).toNat = j := by
    have hsum : marks 0 ω + 1 = (j : ℝ) := by
      rw [hj]
      ring
    rw [hsum, Int.floor_natCast, Int.toNat_natCast]
  have hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A →
      integerCompoundPoisson y arrival marks s ω = (y : ℤ) := by
    intro s hs
    exact reverseIntegerCompoundPoissonConstantBeforeFirstArrival y arrival marks s ω hs
  have hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      integerCompoundPoisson y arrival marks u ω =
        integerCompoundPoisson
          ((y - 1) + (Int.floor (marks 0 ω + 1)).toNat)
          (fun n w => arrival (n + 1) w)
          (fun n w => marks (n + 1) w)
          (Real.toNNReal ((u : ℝ) - A)) ω := by
    intro u hu
    have hEq := integerCompoundPoissonShiftAfterFirstMark y j arrival marks ω hy hMono hTop hj u hu
    rw [← hFloor] at hEq
    simpa [A] using hEq
  have hTailNonnegative :
      (0 : ℤ) ≤ integerCompoundPoisson
        ((y - 1) + (Int.floor (marks 0 ω + 1)).toNat)
        (fun n w => arrival (n + 1) w)
        (fun n w => marks (n + 1) w) 0 ω := by
    have hTailBefore : ((0 : ℝ≥0) : ℝ) <
        ProbabilityTheory.arrival (fun n w => arrival (n + 1) w) 0 ω := by
      simpa [ProbabilityTheory.arrival] using (hPos 1)
    rw [reverseIntegerCompoundPoissonConstantBeforeFirstArrival
      ((y - 1) + (Int.floor (marks 0 ω + 1)).toNat)
      (fun n w => arrival (n + 1) w) (fun n w => marks (n + 1) w)
      (0 : ℝ≥0) ω hTailBefore]
    omega
  simpa [A] using
    reverseLampertiShiftedPathClockNonnegativeStart
      (integerCompoundPoisson y arrival marks)
      (integerCompoundPoisson
        ((y - 1) + (Int.floor (marks 0 ω + 1)).toNat)
        (fun n w => arrival (n + 1) w)
        (fun n w => marks (n + 1) w))
      ω y hy t A (le_of_lt hA0) hFirst hPrefix hShift hTailNonnegative
