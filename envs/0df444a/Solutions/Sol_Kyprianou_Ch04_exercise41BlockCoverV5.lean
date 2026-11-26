-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41BlockCoverV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:05:56.708838+00:00
-- url     : https://prove2.me/submissions/60af1f87-6f0e-4b34-aa68-8b88cdf97aaf

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41FloorCellV4
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    (x : NNReal → ℝ) (δ : NNReal) (hδ : 0 < δ)
    (h : ∀ k : ℕ, Set.Finite
      {s : NNReal | (k : NNReal) * δ ≤ s ∧
        s < (k : NNReal) * δ + δ ∧ x s = 0}) :
    ∀ t : NNReal, Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ x s = 0} := by
  intro t
  have hd : 0 < (δ : ℝ) := by exact_mod_cast hδ
  obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℝ) / (δ : ℝ))
  have htn : (t : ℝ) < (n : ℝ) * (δ : ℝ) := (div_lt_iff₀ hd).mp hn
  let B : Fin n → Set NNReal := fun k =>
    {s | (k.val : NNReal) * δ ≤ s ∧ s < (k.val : NNReal) * δ + δ ∧ x s = 0}
  apply (Set.finite_iUnion (fun k : Fin n => h k.val)).subset
  intro s hs
  have hst : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hs.2.1
  have H := exercise41FloorCellV4 0 (δ : ℝ) (s : ℝ) n hd
    s.coe_nonneg (by simpa only [zero_add] using hst.trans_lt htn)
  dsimp only at H
  let k := Nat.floor (((s : ℝ) - 0) / (δ : ℝ))
  have hk : k < n := Finset.mem_range.mp H.1
  refine Set.mem_iUnion.mpr ⟨⟨k, hk⟩, ?_⟩
  change (k : NNReal) * δ ≤ s ∧ s < (k : NNReal) * δ + δ ∧ x s = 0
  refine ⟨?_, ?_, hs.2.2⟩
  · exact_mod_cast (show (k : ℝ) * (δ : ℝ) ≤ (s : ℝ) by simpa only [zero_add] using H.2.1)
  · have ht : (s : ℝ) < ((k : ℝ) + 1) * (δ : ℝ) := by
      simpa only [zero_add] using H.2.2
    exact_mod_cast (show (s : ℝ) < (k : ℝ) * (δ : ℝ) + (δ : ℝ) by linarith)
