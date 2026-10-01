-- Prove2me | solution 1 for LysgaardCVRP.Shrink.binPackingNumber_union_ge
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:32:46.871992+00:00
-- url     : https://prove2.me/submissions/afdba8af-669d-47f6-8a73-2b8a5742a182

import Definitions.Def_LysgaardCVRP_Shrink_binPackingNumber
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic
open scoped BigOperators
open LysgaardCVRP.Shrink

private lemma packing_exists {n : ℕ} (q : Fin (n+1) → ℕ) (Q : ℝ)
    (hQ : 0 ≤ Q) (S : Finset (Fin (n+1))) (hc : ∀ i ∈ S, (q i : ℝ) ≤ Q) :
    ∃ m : ℕ, ∃ f : Fin (n+1) → ℕ, (∀ i ∈ S, f i < m) ∧
      ∀ b < m, ∑ i ∈ S.filter (fun i => f i = b), (q i : ℝ) ≤ Q := by
  classical
  refine ⟨n+1, Fin.val, fun i hi => i.isLt, ?_⟩
  intro b hb
  let v : Fin (n+1) := ⟨b,hb⟩
  by_cases hv : v ∈ S
  · have he : S.filter (fun i => i.val = b) = {v} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro hi; exact Fin.ext hi.2
      · rintro rfl; exact ⟨hv, rfl⟩
    rw [he, Finset.sum_singleton]
    exact hc v hv
  · have he : S.filter (fun i => i.val = b) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have e : i = v := Fin.ext (Finset.mem_filter.mp hi).2
      exact hv (e ▸ (Finset.mem_filter.mp hi).1)
    rw [he, Finset.sum_empty]
    exact hQ

private lemma packing_mono {n : ℕ} (q : Fin (n+1) → ℕ) (Q : ℝ)
    (hQ : 0 ≤ Q) (S T : Finset (Fin (n+1))) (hST : S ⊆ T)
    (hc : ∀ i ∈ T, (q i : ℝ) ≤ Q) : binPackingNumber q Q S ≤ binPackingNumber q Q T := by
  classical
  have hne := packing_exists q Q hQ T hc
  obtain ⟨f, hf, hcap⟩ := Nat.sInf_mem hne
  apply Nat.sInf_le
  refine ⟨f, fun i hi => hf i (hST hi), ?_⟩
  intro b hb
  refine le_trans ?_ (hcap b hb)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ hST
  · intros; positivity

theorem solution {n : ℕ} (q : Fin (n + 1) → ℕ) (Q : ℝ) (hQ : 0 < Q)
    (hq : ∀ i : Fin (n + 1), i ≠ 0 → 0 < q i ∧ (q i : ℝ) ≤ Q)
    (S T : Finset (Fin (n + 1))) (hS0 : (0 : Fin (n + 1)) ∉ S) (hT0 : (0 : Fin (n + 1)) ∉ T) :
    0 ≤ 2 * (binPackingNumber q Q (S ∪ T) : ℝ) - 2 * (binPackingNumber q Q T : ℝ) := by
  have h := packing_mono q Q hQ.le T (S ∪ T) Finset.subset_union_right ?_
  · exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) (by norm_num))
  · intro i hi
    apply (hq i ?_).2
    rintro rfl
    simp [hS0,hT0] at hi
