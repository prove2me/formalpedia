-- Prove2me | solution 1 for MetricTSPSublinear.sample_distance_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:22:33.550086+00:00
-- url     : https://prove2.me/submissions/bd5d2f45-7ef6-45df-918c-7f1330171bf5

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSP_model

theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (π : Equiv.Perm (Fin n)) (S0 : Finset (Fin n)) (hS0 : S0.Nonempty) (k : ℕ)
    (hwin : ∀ i : Fin n, ∃ j < k, π ((finRotate n)^[j] i) ∈ S0) :
    ∑ v, S0.inf' hS0 (fun s => d v s) ≤ k * MetricTSP.tourCost d π := by
  set rot := finRotate n
  set c : Fin n → ℝ := fun i => d (π i) (π (rot i)) with hc
  have hnn : ∀ x y, 0 ≤ d x y := by
    intro x y
    have h1 := hd.2.2 x y x
    rw [(hd.1 x x).mpr rfl, hd.2.1 y x] at h1
    linarith
  have chain : ∀ i : Fin n, ∀ j : ℕ, d (π i) (π (rot^[j] i)) ≤ ∑ t ∈ Finset.range j, c (rot^[t] i) := by
    intro i j
    induction j with
    | zero => simp [(hd.1 _ _).mpr rfl]
    | succ j ih =>
      rw [Finset.sum_range_succ, Function.iterate_succ_apply']
      calc d (π i) (π (rot (rot^[j] i))) ≤ d (π i) (π (rot^[j] i)) + d (π (rot^[j] i)) (π (rot (rot^[j] i))) :=
            hd.2.2 _ _ _
        _ ≤ _ := by simp only [hc]; linarith
  have per : ∀ i : Fin n, S0.inf' hS0 (fun s => d (π i) s) ≤ ∑ t ∈ Finset.range k, c (rot^[t] i) := by
    intro i
    obtain ⟨j, hjk, hj⟩ := hwin i
    calc S0.inf' hS0 (fun s => d (π i) s) ≤ d (π i) (π (rot^[j] i)) := Finset.inf'_le _ hj
      _ ≤ ∑ t ∈ Finset.range j, c (rot^[t] i) := chain i j
      _ ≤ ∑ t ∈ Finset.range k, c (rot^[t] i) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hjk.le)
          intro t _ _; exact hnn _ _
  calc ∑ v, S0.inf' hS0 (fun s => d v s) = ∑ i, S0.inf' hS0 (fun s => d (π i) s) :=
        (Equiv.sum_comp π (fun v => S0.inf' hS0 (fun s => d v s))).symm
    _ ≤ ∑ i, ∑ t ∈ Finset.range k, c (rot^[t] i) := Finset.sum_le_sum fun i _ => per i
    _ = ∑ t ∈ Finset.range k, ∑ i, c (rot^[t] i) := Finset.sum_comm
    _ = ∑ t ∈ Finset.range k, ∑ i, c i := by
        apply Finset.sum_congr rfl; intro t _
        rw [← Equiv.Perm.coe_pow]
        exact Equiv.sum_comp (rot ^ t) c
    _ = k * MetricTSP.tourCost d π := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; rfl
