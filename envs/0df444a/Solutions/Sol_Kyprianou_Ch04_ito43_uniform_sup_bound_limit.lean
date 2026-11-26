-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_uniform_sup_bound_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:57:20.626634+00:00
-- url     : https://prove2.me/submissions/3ceb918b-e8f6-4a2e-8847-7244ff035303

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution (E : ℕ → NNReal → ℝ) (T : NNReal)
    (hb : ∀ n, BddAbove (Set.range (fun t : Set.Iic T => |E n t|)))
    (hE : ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ t ≤ T, |E n t| < e) :
    let C : ℕ → ℝ := fun n => sSup (Set.range (fun t : Set.Iic T => |E n t|))
    Tendsto C atTop (nhds 0) ∧ ∀ n t, t ≤ T → |E n t| ≤ |C n| := by
  intro C
  have hbound (n : ℕ) (t : NNReal) (ht : t ≤ T) :
      |E n t| ≤ C n := le_csSup (hb n) ⟨⟨t,ht⟩,rfl⟩
  have hnon (n : ℕ) : 0 ≤ C n :=
    (abs_nonneg _).trans (hbound n 0 (by positivity))
  refine ⟨?_, fun n t ht => by rw [abs_of_nonneg (hnon n)]; exact hbound n t ht⟩
  apply Metric.tendsto_atTop.mpr
  intro e he
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hE (e/2) (by positivity))
  refine ⟨N,fun n hn => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hnon n)]
  have h : C n ≤ e/2 := by
    apply csSup_le
    · exact ⟨_,⟨⟨0,Set.mem_Iic.mpr (by positivity)⟩,rfl⟩⟩
    · rintro _ ⟨t,rfl⟩
      exact (hN n hn t.1 t.2).le
  linarith
