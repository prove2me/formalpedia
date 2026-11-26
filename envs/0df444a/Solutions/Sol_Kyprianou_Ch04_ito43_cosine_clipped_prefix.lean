-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_clipped_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:46:29.334677+00:00
-- url     : https://prove2.me/submissions/9e6e845b-9075-4b0e-afcb-ed95c4c35af9

import Mathlib
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (X : NNReal → ℝ) (q : ℝ → ℝ) (h0 : q 0 = 0)
    (C : ℝ) (hC : 0 ≤ C) (hq : ∀ z, 0 ≤ q z ∧ q z ≤ C)
    (T t : NNReal) (ht : t ≤ T) (n : ℕ) (hn : 0 < n) :
    let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    ∃ j ≤ n, |(t:ℝ)-(u j:ℝ)| ≤ (T:ℝ)/(n:ℝ) ∧
      |(∑ k ∈ Finset.range n, q (X (v (k+1))-X (v k))) -
       (∑ k ∈ Finset.range j, q (X (u (k+1))-X (u k)))| ≤ C := by
  intro u v
  classical
  have hu : Monotone u := by
    intro i j hij
    dsimp [u]
    gcongr
  have hu0 : u 0 = 0 := by simp [u]
  have hun : u n = T := by
    have hn' : (n:NNReal) ≠ 0 := by exact_mod_cast hn.ne'
    dsimp [u]
    exact mul_div_cancel_right₀ T hn'
  by_cases ht0 : t = 0
  · subst t
    exact ⟨0, Nat.zero_le n, by simp [hu0]; positivity, by simp [v,h0,hC]⟩
  have hex : ∃ i, t ≤ u i := ⟨n,hun ▸ ht⟩
  let i := Nat.find hex
  have hi : t ≤ u i := Nat.find_spec hex
  have hin : i ≤ n := Nat.find_min' hex (hun ▸ ht)
  have hi0 : 0 < i := by
    by_contra h
    have he : i = 0 := by omega
    rw [he,hu0] at hi
    exact ht0 (le_antisymm hi bot_le)
  let j := i-1
  have hj : j+1 = i := Nat.sub_add_cancel hi0
  have hjn : j < n := by omega
  have hjt : u j < t := lt_of_not_ge (Nat.find_min hex (by omega : j < i))
  have hit : t ≤ u (j+1) := by rw [hj]; exact hi
  have hw : (u (j+1):ℝ)-(u j:ℝ) = (T:ℝ)/(n:ℝ) := by
    dsimp [u]
    push_cast
    ring
  have hclock : |(t:ℝ)-(u j:ℝ)| ≤ (T:ℝ)/(n:ℝ) := by
    have h1 : (u j:ℝ) ≤ (t:ℝ) := by exact_mod_cast hjt.le
    have h2 : (t:ℝ) ≤ (u (j+1):ℝ) := by exact_mod_cast hit
    rw [abs_of_nonneg (sub_nonneg.mpr h1),← hw]
    linarith
  refine ⟨j,hjn.le,hclock,?_⟩
  let F : ℕ → ℝ := fun k => q (X (v (k+1))-X (v k))
  let H : ℕ → ℝ := fun k => q (X (u (k+1))-X (u k))
  have hf : ∑ k ∈ Finset.range n, F k = ∑ k ∈ Finset.range (j+1), F k := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k hk hnot
    have hk' : j+1 ≤ k := by simpa using hnot
    have htk := hit.trans (hu hk')
    have htk1 := htk.trans (hu (Nat.le_succ k))
    simp [F,v,min_eq_left htk,min_eq_left htk1,h0]
  have he : ∑ k ∈ Finset.range j, F k = ∑ k ∈ Finset.range j, H k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k+1 ≤ j := Finset.mem_range.mp hk
    have h1 := (hu hk').trans hjt.le
    have h2 := (hu (Nat.le_succ k)).trans h1
    simp [F,H,v,min_eq_right h1,min_eq_right h2]
  change |(∑ k ∈ Finset.range n, F k)-(∑ k ∈ Finset.range j,H k)| ≤ C
  rw [hf,Finset.sum_range_succ,he,add_sub_cancel_left]
  change |q (X (v (j+1))-X (v j))| ≤ C
  rw [abs_of_nonneg (hq _).1]
  exact (hq _).2
