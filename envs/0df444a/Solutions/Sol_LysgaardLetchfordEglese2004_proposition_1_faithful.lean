-- Prove2me | solution 1 for LysgaardLetchfordEglese2004.proposition_1_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:41:07.895965+00:00
-- url     : https://prove2.me/submissions/3b4c6e35-c1c3-48af-bb3c-8f0d42d60d0c

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_binPackingNumber
import Definitions.Def_LysgaardCVRP_Shrink_SafeToShrink

open LysgaardCVRP.Shrink

namespace LY85

theorem cut_eq {n : ℕ} (x : Sym2 (Fin (n + 1)) → ℝ) (A : Finset (Fin (n + 1))) :
    cut x A = ∑ i, ∑ j, if i ∈ A ∧ j ∉ A then x s(i, j) else 0 := by
  unfold cut
  have : ∀ i, (∑ j, if i ∈ A ∧ j ∉ A then x s(i, j) else 0) =
      if i ∈ A then ∑ j ∈ Aᶜ, x s(i, j) else 0 := by
    intro i
    split_ifs with h
    · rw [← Finset.sum_filter]; congr 1; ext j; simp [h]
    · simp [h]
  simp_rw [this]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem cut_submod {n : ℕ} (x : Sym2 (Fin (n + 1)) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (A B : Finset (Fin (n + 1))) :
    cut x (A ∪ B) + cut x (A ∩ B) ≤ cut x A + cut x B := by
  rw [cut_eq, cut_eq, cut_eq, cut_eq, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro i _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro j _
  have := hx s(i, j)
  simp only [Finset.mem_union, Finset.mem_inter]
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> by_cases ja : j ∈ A <;> by_cases jb : j ∈ B <;>
    simp [ha, hb, ja, jb] <;> linarith

theorem bp_mono {n : ℕ} (q : Fin (n + 1) → ℕ) (Q : ℝ) (hQ : 0 < Q)
    (hq : ∀ i : Fin (n + 1), i ≠ 0 → 0 < q i ∧ (q i : ℝ) ≤ Q)
    {T U : Finset (Fin (n + 1))} (hTU : T ⊆ U) (hU : (0 : Fin (n + 1)) ∉ U) :
    binPackingNumber q Q T ≤ binPackingNumber q Q U := by
  unfold binPackingNumber
  have hne : (n + 1) ∈ {m : ℕ | ∃ f : Fin (n + 1) → ℕ, (∀ i ∈ U, f i < m) ∧
      ∀ b < m, ∑ i ∈ U.filter (fun i => f i = b), (q i : ℝ) ≤ Q} := by
    refine ⟨fun i => i.val, fun i _ => i.isLt, fun b hb => ?_⟩
    have hsub : U.filter (fun i : Fin (n + 1) => i.val = b) ⊆ {⟨b, hb⟩} := by
      intro i hi; simp at hi ⊢; ext; simp [hi.2]
    rcases Finset.subset_singleton_iff.mp hsub with h | h
    · rw [h]; simp; exact hQ.le
    · rw [h, Finset.sum_singleton]
      have hm : (⟨b, hb⟩ : Fin (n + 1)) ∈ U := by
        have : (⟨b, hb⟩ : Fin (n + 1)) ∈ U.filter (fun i : Fin (n + 1) => i.val = b) := by
          rw [h]; simp
        exact (Finset.mem_filter.mp this).1
      exact (hq _ (fun h0 => hU (h0 ▸ hm))).2
  obtain ⟨f, hf1, hf2⟩ := Nat.sInf_mem ⟨_, hne⟩
  apply Nat.sInf_le
  refine ⟨f, fun i hi => hf1 i (hTU hi), fun b hb => le_trans ?_ (hf2 b hb)⟩
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i; simp only [Finset.mem_filter]; exact fun h => ⟨hTU h.1, h.2⟩
  · intros; positivity

end LY85

open LY85 in
theorem solution {n : ℕ} (q : Fin (n + 1) → ℕ) (Q : ℝ) (hQ : 0 < Q)
    (hq : ∀ i : Fin (n + 1), i ≠ 0 → 0 < q i ∧ (q i : ℝ) ≤ Q)
    (x : Sym2 (Fin (n + 1)) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hdeg : ∀ i : Fin (n + 1), i ≠ 0 → cut x {i} = 2)
    (hub : ∀ i j : Fin (n + 1), i ≠ 0 → j ≠ 0 → i ≠ j → x s(i, j) ≤ 1)
    (hub0 : ∀ j : Fin (n + 1), j ≠ 0 → x s(0, j) ≤ 2)
    (S : Finset (Fin (n + 1))) (hS0 : (0 : Fin (n + 1)) ∉ S) (hS : cut x S ≤ 2)
    (hR : ∀ R : Finset (Fin (n + 1)), R ⊆ S → R.Nonempty → R ≠ S → 2 ≤ cut x R) :
    SafeToShrink x (binPackingNumber q Q) S := by
  intro T hT0 hT2 hviol
  by_cases hdisj : Disjoint S T
  · exact ⟨T, hT0, hT2, Or.inr hdisj, le_rfl⟩
  by_cases hsub : S ⊆ T
  · exact ⟨T, hT0, hT2, Or.inl hsub, le_rfl⟩
  refine ⟨T ∪ S, ?_, ?_, Or.inl Finset.subset_union_right, ?_⟩
  · simp [hT0, hS0]
  · exact hT2.trans (Finset.card_le_card Finset.subset_union_left)
  · have hR' := hR (T ∩ S) Finset.inter_subset_right
      (by rw [Finset.inter_comm]; exact Finset.not_disjoint_iff_nonempty_inter.mp hdisj)
      (fun h => hsub (h ▸ Finset.inter_subset_left))
    have hsm := cut_submod x hx T S
    have hbp := bp_mono q Q hQ hq (Finset.subset_union_left (s₁ := T) (s₂ := S))
      (by simp [hT0, hS0])
    unfold violation
    have : ((binPackingNumber q Q T : ℕ) : ℝ) ≤ (binPackingNumber q Q (T ∪ S) : ℝ) := by
      exact_mod_cast hbp
    linarith
