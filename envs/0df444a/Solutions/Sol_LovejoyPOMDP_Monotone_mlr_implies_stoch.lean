-- Prove2me | solution 1 for LovejoyPOMDP.Monotone.mlr_implies_stoch
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:11:12.845701+00:00
-- url     : https://prove2.me/submissions/4e18104e-fe99-4ad2-8d7b-b80c5bf70fdb

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Orders

set_option autoImplicit false
open LovejoyPOMDP.Monotone

theorem solution {X : Type*} [Fintype X] [LinearOrder X] {π π' : X → ℝ}
    (hπ : π ∈ stdSimplex ℝ X) (hπ' : π' ∈ stdSimplex ℝ X) (h : MLRGE π π') :
    StochGE π π' := by
  intro q
  have h1 : (∑ i ∈ Finset.univ.filter (fun i => q ≤ i), π i)
      + ∑ i ∈ Finset.univ.filter (fun i => ¬ q ≤ i), π i = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not]; exact hπ.2
  have h1' : (∑ i ∈ Finset.univ.filter (fun i => q ≤ i), π' i)
      + ∑ i ∈ Finset.univ.filter (fun i => ¬ q ≤ i), π' i = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not]; exact hπ'.2
  have key : (∑ i ∈ Finset.univ.filter (fun i => ¬ q ≤ i), π i) * (∑ i ∈ Finset.univ.filter (fun i => q ≤ i), π' i)
      ≤ (∑ i ∈ Finset.univ.filter (fun i => q ≤ i), π i) * (∑ i ∈ Finset.univ.filter (fun i => ¬ q ≤ i), π' i) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    have hji : j ≤ i := le_trans (not_le.mp hj).le hi
    exact h i j hji
  set A := ∑ i ∈ Finset.univ.filter (fun i => q ≤ i), π i
  set B := ∑ i ∈ Finset.univ.filter (fun i => ¬ q ≤ i), π i
  set A' := ∑ i ∈ Finset.univ.filter (fun i => q ≤ i), π' i
  set B' := ∑ i ∈ Finset.univ.filter (fun i => ¬ q ≤ i), π' i
  have hB : B = 1 - A := by linarith
  have hB' : B' = 1 - A' := by linarith
  rw [hB, hB'] at key
  nlinarith [key]
