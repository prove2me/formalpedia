-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_grid_step_integral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:33:21.853837+00:00
-- url     : https://prove2.me/submissions/edc1b170-d399-49ee-b39e-4631ccaee637

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

/-- Exact integral of the bounded right-endpoint step approximation. -/
theorem solution
    (mu : Measure Real) (a b : Real)
    [IsFiniteMeasure (mu.restrict (Ioc a b))]
    (f : Real → Complex) (u : Nat → Real) (N : Nat) (right : Bool)
    (hu : Monotone u) (h0 : u 0 = a) (hN : u N = b) :
    (∫ x in Ioc a b, ∑ i ∈ Finset.range N,
      (Ioc (u i) (u (i+1))).indicator
        (fun _ : Real => f (if right then u (i+1) else u i)) x ∂mu) =
    ∑ i ∈ Finset.range N,
      (mu (Ioc (u i) (u (i+1)))).toReal • f (if right then u (i+1) else u i) := by
  classical
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    have hsub : Ioc (u i) (u (i+1)) ⊆ Ioc a b := by
      intro x hx
      have hlo := hu (Nat.zero_le i)
      have hhi := hu (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
      rw [h0] at hlo
      rw [hN] at hhi
      exact ⟨hlo.trans_lt hx.1, hx.2.trans hhi⟩
    rw [integral_indicator measurableSet_Ioc, integral_const]
    simp only [Measure.real_def, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter]
    rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.mpr hsub]
  · intro i hi
    exact (integrable_const _).indicator measurableSet_Ioc
