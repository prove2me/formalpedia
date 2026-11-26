-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41DenseCountLowerV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:43:36.100124+00:00
-- url     : https://prove2.me/submissions/83a663ef-1948-41b7-8eea-a2d460ee0ec9

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41DenseRightHitV4
import Theorems.Thm_Kyprianou_Ch04_exercise41SuccessfulIndicatorSumV3
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (S : Finset NNReal) (a h e : ℝ) (n : ℕ)
    (he : 0 < e) (j : NNReal → ℕ)
    (hc : ∀ s ∈ S, j s ∈ Finset.range n ∧
      a + (j s : ℝ) * h ≤ (s : ℝ) ∧
      (s : ℝ) < a + ((j s : ℝ) + 1) * h)
    (hinj : Set.InjOn j (S : Set NNReal))
    (hr : ∀ s ∈ S, ContinuousWithinAt x (Ici s) s)
    (hz : ∀ s ∈ S, x s = 0) :
    let A : ℕ → ℕ → Set Unit := fun m i =>
      {w | ∃ k < m, a + (i : ℝ) * h ≤ (q k : ℝ) ∧
        (q k : ℝ) < a + ((i : ℝ) + 1) * h ∧ |x (q k)| < e}
    (S.card : ℝ≥0∞) ≤ ⨆ m : ℕ, ∑ i ∈ Finset.range n,
      (A m i).indicator (fun _ : Unit => (1 : ℝ≥0∞)) () := by
  dsimp only
  let A : ℕ → ℕ → Set Unit := fun m i =>
    {w | ∃ k < m, a + (i : ℝ) * h ≤ (q k : ℝ) ∧
      (q k : ℝ) < a + ((i : ℝ) + 1) * h ∧ |x (q k)| < e}
  change (S.card : ℝ≥0∞) ≤ ⨆ m : ℕ, ∑ i ∈ Finset.range n,
    (A m i).indicator (fun _ : Unit => (1 : ℝ≥0∞)) ()
  have hhit (s : NNReal) (hs : s ∈ S) :
      ∃ k : ℕ, a + (j s : ℝ) * h ≤ (q k : ℝ) ∧
        (q k : ℝ) < a + ((j s : ℝ) + 1) * h ∧ |x (q k)| < e := by
    obtain ⟨k, hk, hu, hv⟩ := exercise41DenseRightHitV4 x q hq s
      (a + ((j s : ℝ) + 1) * h) e (hc s hs).2.2 he (hr s hs) (hz s hs)
    exact ⟨k, (hc s hs).2.1.trans (by exact_mod_cast hk), hu, hv⟩
  have hev : ∀ s ∈ S, ∀ᶠ m in atTop, () ∈ A m (j s) := by
    intro s hs
    obtain ⟨k, hl, hu, hv⟩ := hhit s hs
    filter_upwards [eventually_gt_atTop k] with m hm
    exact ⟨k, hm, hl, hu, hv⟩
  have hAll : ∀ᶠ m in atTop, ∀ s ∈ S, () ∈ A m (j s) :=
    (Filter.eventually_all_finset S).2 hev
  obtain ⟨m, hm⟩ := hAll.exists
  let T := (Finset.range n).filter fun i => () ∈ A m i
  have hcard : S.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn j _ hinj
    intro s hs
    exact Finset.mem_filter.mpr ⟨(hc s hs).1, hm s hs⟩
  calc
    (S.card : ℝ≥0∞) ≤ (T.card : ℝ≥0∞) := by exact_mod_cast hcard
    _ = ∑ i ∈ Finset.range n, (A m i).indicator (fun _ : Unit => (1 : ℝ≥0∞)) () := by
      symm
      rw [exercise41SuccessfulIndicatorSumV3]
      congr
    _ ≤ _ := le_iSup (fun m : ℕ => ∑ i ∈ Finset.range n,
      (A m i).indicator (fun _ : Unit => (1 : ℝ≥0∞)) ()) m
