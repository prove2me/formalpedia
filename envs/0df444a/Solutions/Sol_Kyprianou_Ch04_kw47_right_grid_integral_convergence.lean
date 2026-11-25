-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_right_grid_integral_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:08:26.456608+00:00
-- url     : https://prove2.me/submissions/b910126d-0c9d-4477-b78b-2f1653f54817

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_grid_cell_exists_unique
import Theorems.Thm_Kyprianou_Ch04_kw47_grid_step_integral_exact
open MeasureTheory Filter Set Topology
set_option autoImplicit false

/-- A bounded right-continuous function is approximated by right endpoint
grid sums for any measure finite on the covered half-open interval. -/
theorem solution
    (mu : Measure Real) (a b : Real)
    [IsFiniteMeasure (mu.restrict (Ioc a b))]
    (f : Real → Real) (B : Real)
    (hf : Measurable f) (hB : ∀ x, ‖f x‖ ≤ B)
    (hRight : ∀ x, ContinuousWithinAt f (Ici x) x)
    (u : Nat → Nat → Real) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n → u n (i+1) - u n i ≤ delta n) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      (mu (Ioc (u n i) (u n (i+1)))).toReal * f (u n (i+1)))
      atTop (nhds (∫ x in Ioc a b, f x ∂mu)) := by
  classical
  let nu := mu.restrict (Ioc a b)
  let g : Nat → Real → Real := fun n x =>
    ∑ i ∈ Finset.range (N n),
      (Ioc (u n i) (u n (i+1))).indicator
        (fun _ : Real => f (u n (i+1))) x
  have hEval (n : Nat) (x : Real) (hx : x ∈ Ioc a b) :
      ∃ y, x ≤ y ∧ y - x ≤ delta n ∧ g n x = f y := by
    obtain ⟨i, hi, hxi, huniq⟩ := Kyprianou.Ch04.kw47_grid_cell_exists_unique (u n) (hu n) (N n) x
      (by simpa only [h0 n, hN n] using hx)
    refine ⟨u n (i+1), hxi.2, ?_, ?_⟩
    · have hm := hMesh n i (Finset.mem_range.mp hi)
      linarith [hxi.1]
    · dsimp only [g]
      rw [Finset.sum_eq_single_of_mem i hi]
      · exact Set.indicator_of_mem hxi _
      · intro j hj hne
        have hn : x ∉ Ioc (u n j) (u n (j+1)) :=
          fun h => hne (huniq j hj h)
        simp [Set.indicator, hn]
  have hGMeas (n : Nat) : Measurable (g n) := by
    unfold g
    exact Finset.measurable_sum _ (fun i hi =>
      measurable_const.indicator measurableSet_Ioc)
  have hBound (n : Nat) : ∀ᵐ x ∂nu, ‖g n x‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    obtain ⟨y, hy, hd, he⟩ := hEval n x hx
    rw [he]
    exact hB y
  have hLim : ∀ᵐ x ∂nu, Tendsto (fun n => g n x) atTop (nhds (f x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    choose y hy hd he using fun n => hEval n x hx
    have hyLim : Tendsto y atTop (nhds x) := by
      apply Metric.tendsto_atTop.mpr
      intro eps heps
      obtain ⟨k, hk⟩ := Metric.tendsto_atTop.mp hDelta eps heps
      refine ⟨k, fun n hn => ?_⟩
      have h := hk n hn
      rw [Real.dist_eq, sub_zero] at h
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hy n))]
      exact lt_of_le_of_lt (hd n) (lt_of_le_of_lt (le_abs_self _) h)
    have hyRight : Tendsto y atTop (nhdsWithin x (Ici x)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hyLim, Eventually.of_forall hy⟩
    have h := (hRight x).tendsto.comp hyRight
    have hEq : (fun n => g n x) = fun n => f (y n) := funext he
    rw [hEq]
    exact h
  have hIntegral := tendsto_integral_of_dominated_convergence (fun _ => B)
    (fun n => (hGMeas n).aestronglyMeasurable) (integrable_const B)
    hBound hLim
  have hExact (n : Nat) : (∫ x, g n x ∂nu) =
      ∑ i ∈ Finset.range (N n),
        (mu (Ioc (u n i) (u n (i+1)))).toReal * f (u n (i+1)) :=
    Kyprianou.Ch04.kw47_grid_step_integral_exact mu a b f
      (u n) (N n) (hu n) (h0 n) (hN n)
  simp_rw [hExact] at hIntegral
  exact hIntegral
