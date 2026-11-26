-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_complex_quadrature
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:42:31.247906+00:00
-- url     : https://prove2.me/submissions/675e3075-1afa-496b-8585-923af96b3139

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_eval_distance
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_step_integral_exact
open MeasureTheory Filter Set Topology
set_option autoImplicit false

/-- Both endpoint quadratures converge for a bounded complex function
continuous from the chosen side almost everywhere for the cell measure. -/
theorem solution
    (mu : Measure Real) (a b : Real)
    [IsFiniteMeasure (mu.restrict (Ioc a b))]
    (f : Real → Complex) (B : Real)
    (hf : Measurable f) (hB : ∀ x, ‖f x‖ ≤ B)
    (u : Nat → Nat → Real) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n → u n (i+1)-u n i ≤ delta n)
    (right : Bool)
    (hCont : ∀ᵐ x ∂(mu.restrict (Ioc a b)),
      ContinuousWithinAt f (if right then Ici x else Iic x) x) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      (mu (Ioc (u n i) (u n (i+1)))).toReal •
        f (if right then u n (i+1) else u n i))
      atTop (nhds (∫ x in Ioc a b, f x ∂mu)) := by
  classical
  let nu := mu.restrict (Ioc a b)
  let g : Nat → Real → Complex := fun n x =>
    ∑ i ∈ Finset.range (N n), (Ioc (u n i) (u n (i+1))).indicator
      (fun _ : Real => f (if right then u n (i+1) else u n i)) x
  have hEval (n : Nat) (x : Real) (hx : x ∈ Ioc a b) :
      ∃ y, y ∈ (if right then Ici x else Iic x) ∧
        dist y x ≤ delta n ∧ g n x = f y :=
    Kyprianou.Ch04.kw48_grid_eval_distance f (u n) (N n) (hu n)
      (delta n) (hMesh n) right x
      (by simpa only [h0 n,hN n] using hx)
  have hMeas (n : Nat) : Measurable (g n) := by
    unfold g
    exact Finset.measurable_sum _ (fun i hi =>
      measurable_const.indicator measurableSet_Ioc)
  have hBound (n : Nat) : ∀ᵐ x ∂nu, ‖g n x‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    obtain ⟨y,hy,hd,he⟩ := hEval n x hx
    rw [he]
    exact hB y
  have hLim : ∀ᵐ x ∂nu, Tendsto (fun n => g n x) atTop (nhds (f x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hCont] with x hx hc
    choose y hy hd he using fun n => hEval n x hx
    have hyLim : Tendsto y atTop (nhds x) := by
      apply Metric.tendsto_atTop.mpr
      intro eps heps
      obtain ⟨k,hk⟩ := Metric.tendsto_atTop.mp hDelta eps heps
      refine ⟨k,fun n hn => ?_⟩
      have h := hk n hn
      rw [Real.dist_eq,sub_zero] at h
      exact (hd n).trans_lt ((le_abs_self _).trans_lt h)
    have hySide : Tendsto y atTop (nhdsWithin x
        (if right then Ici x else Iic x)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hyLim,Eventually.of_forall hy⟩
    have h := hc.tendsto.comp hySide
    rw [show (fun n => g n x) = fun n => f (y n) from funext he]
    exact h
  have hInt := tendsto_integral_of_dominated_convergence (fun _ => B)
    (fun n => (hMeas n).aestronglyMeasurable) (integrable_const B) hBound hLim
  have hExact (n : Nat) : (∫ x, g n x ∂nu) =
      ∑ i ∈ Finset.range (N n), (mu (Ioc (u n i) (u n (i+1)))).toReal •
        f (if right then u n (i+1) else u n i) :=
    Kyprianou.Ch04.kw48_grid_step_integral_exact mu a b f (u n) (N n)
      right (hu n) (h0 n) (hN n)
  simp_rw [hExact] at hInt
  exact hInt
