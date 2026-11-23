-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiFirstArrivalShiftedTailPathwise
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T16:57:09.36471+00:00
-- url     : https://prove2.me/submissions/ab6b38f1-4537-409e-a4ee-2f550d8904fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ProbabilityTheory_lt_jumpCount_iff
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_strictMono_arrival
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_tendsto_arrival
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
import Theorems.Thm_Kyprianou_Ch01_reverseIntegerCompoundPoissonConstantBeforeFirstArrival
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstMarkOffspringSupportAE
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiShiftedPathClock

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Finset
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
set_option linter.unusedVariables false

lemma sourceAfterFirstMark
    {Ω : Type*} (y j : ℕ) (arrival marks : ℕ → Ω → ℝ) (ω : Ω)
    (hy : 0 < y)
    (hMono : StrictMono (fun n => ProbabilityTheory.arrival arrival n ω))
    (hTop : Tendsto (fun n => ProbabilityTheory.arrival arrival n ω) atTop atTop)
    (hMark : marks 0 ω = (j : ℝ) - 1)
    (u : ℝ≥0)
    (hu : ProbabilityTheory.arrival arrival 0 ω ≤ (u : ℝ)) :
    integerCompoundPoisson y arrival marks u ω =
      integerCompoundPoisson ((y - 1) + j)
        (fun n w => arrival (n + 1) w)
        (fun n w => marks (n + 1) w)
        (Real.toNNReal ((u : ℝ) - ProbabilityTheory.arrival arrival 0 ω)) ω := by
  set A : ℝ := ProbabilityTheory.arrival arrival 0 ω
  set T : ℕ → ℝ := fun n => ProbabilityTheory.arrival arrival n ω
  set Tshift : ℕ → ℝ := fun n =>
    ProbabilityTheory.arrival (fun k w => arrival (k + 1) w) n ω
  have hTshift : ∀ n, Tshift n = T (n + 1) - A := by
    intro n
    have hs := sum_range_succ' (fun i => arrival i ω) (n + 1)
    have hsum : A + Tshift n = T (n + 1) := by
      simp only [A, Tshift, T, ProbabilityTheory.arrival, Nat.zero_add, Finset.sum_range_one]
      rw [add_comm]
      exact hs.symm
    linarith
  have hMonoS : StrictMono Tshift := by
    intro a b hab
    rw [hTshift a, hTshift b]
    exact sub_lt_sub_right (hMono (Nat.succ_lt_succ hab)) A
  have hTopS : Tendsto Tshift atTop atTop := by
    have hcomp : Tendsto (fun n => T (n + 1)) atTop atTop :=
      hTop.comp (tendsto_add_atTop_nat 1)
    have hfun : Tshift = fun n => T (n + 1) - A := by
      funext n
      exact hTshift n
    rw [hfun]
    exact tendsto_atTop_add_const_right atTop (-A) hcomp
  have hIff := lt_jumpCount_iff hMono hTop
  have hIffS := lt_jumpCount_iff hMonoS hTopS
  set N : ℕ := jumpCount T (u : ℝ)
  have hN : 0 < N := (hIff 0 (u : ℝ)).mpr hu
  have hJc : jumpCount Tshift ((u : ℝ) - A) = N - 1 := by
    have hlt : ∀ n, n < jumpCount Tshift ((u : ℝ) - A) ↔ n < N - 1 := by
      intro n
      rw [hIffS n ((u : ℝ) - A), hTshift n, sub_le_sub_iff_right, ← hIff (n + 1) (u : ℝ)]
      exact Nat.lt_sub_iff_add_lt.symm
    refine le_antisymm ?_ ?_
    · by_contra h
      exact lt_irrefl (N - 1) ((hlt (N - 1)).mp (Nat.lt_of_not_ge h))
    · by_contra h
      exact lt_irrefl _ ((hlt _).mpr (Nat.lt_of_not_ge h))
  have htime : ((Real.toNNReal ((u : ℝ) - A) : ℝ≥0) : ℝ) = (u : ℝ) - A :=
    Real.coe_toNNReal ((u : ℝ) - A) (sub_nonneg.mpr hu)
  have hsum := sum_range_succ' (fun i => marks i ω) (N - 1)
  have hsucc : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.succ_le_of_lt hN)
  rw [hsucc] at hsum
  have hreal :
      (y : ℝ) + ∑ n ∈ range N, marks n ω =
        (((y - 1) + j : ℕ) : ℝ) + ∑ n ∈ range (N - 1), marks (n + 1) ω := by
    rw [hsum, hMark]
    have hy1 : 1 ≤ y := Nat.succ_le_of_lt hy
    have hheight : (((y - 1) + j : ℕ) : ℝ) = (y : ℝ) + (j : ℝ) - 1 := by
      rw [Nat.cast_add, Nat.cast_sub hy1]
      ring
    rw [hheight]
    ring
  simp only [integerCompoundPoisson, compoundPoisson, piecewisePath, zero_mul, add_zero,
    zero_add]
  rw [show jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (u : ℝ) = N by rfl]
  rw [htime, hJc]
  exact congrArg Int.floor hreal

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
    have hEq := sourceAfterFirstMark y j arrival marks ω hy hMono hTop hj u hu
    rw [← hFloor] at hEq
    simpa [A] using hEq
  simpa [A] using
    reverseLampertiShiftedPathClock
      (integerCompoundPoisson y arrival marks)
      (integerCompoundPoisson
        ((y - 1) + (Int.floor (marks 0 ω + 1)).toNat)
        (fun n w => arrival (n + 1) w)
        (fun n w => marks (n + 1) w))
      ω y hy t A (le_of_lt hA0) hFirst hPrefix hShift
