-- Prove2me | solution 1 for Kyprianou.Ch01.integerCompoundPoissonShiftAfterFirstMark
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:06:20.425395+00:00
-- url     : https://prove2.me/submissions/3cda0741-6985-478a-8635-52b089d967f0

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_ProbabilityTheory_lt_jumpCount_iff
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Finset
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

private theorem firstArrivalShiftJumpCount
    {Ω : Type*} (arrival : ℕ → Ω → ℝ) (ω : Ω)
    (hMono : StrictMono (fun n => ProbabilityTheory.arrival arrival n ω))
    (hTop : Tendsto (fun n => ProbabilityTheory.arrival arrival n ω) atTop atTop)
    (u : ℝ≥0) (hu : ProbabilityTheory.arrival arrival 0 ω ≤ (u : ℝ)) :
    jumpCount (fun n => ProbabilityTheory.arrival (fun k w => arrival (k + 1) w) n ω)
      ((u : ℝ) - ProbabilityTheory.arrival arrival 0 ω) =
    jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (u : ℝ) - 1 := by
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
  exact hJc

theorem solution
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
  set N : ℕ := jumpCount T (u : ℝ)
  have hN : 0 < N := ((lt_jumpCount_iff hMono hTop) 0 (u : ℝ)).mpr hu
  have hJc : jumpCount Tshift ((u : ℝ) - A) = N - 1 := by
    simpa [Tshift, T, N, A] using
      firstArrivalShiftJumpCount arrival ω hMono hTop u hu
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

