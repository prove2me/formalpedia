-- Prove2me | solution 1 for LysgaardCVRP.Shrink.crossing_violation_le
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:35:55.994897+00:00
-- url     : https://prove2.me/submissions/364191c5-7925-4f6c-a528-b6f10b204dc3

import Definitions.Def_LysgaardCVRP_Shrink_SafeToShrink
import Definitions.Def_LysgaardCVRP_Shrink_binPackingNumber
import Mathlib.Order.Lattice.Nat
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Mathlib.Tactic
open scoped BigOperators
open LysgaardCVRP.Shrink

private lemma cut_formula {n : ℕ} (x : Sym2 (Fin (n+1)) → ℝ)
    (S : Finset (Fin (n+1))) :
    cut x S = ∑ i, ∑ j, if i ∈ S ∧ j ∉ S then x s(i,j) else 0 := by
  classical
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    ← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hc : (Finset.univ.filter (fun i => i ∉ S)) = Sᶜ := by ext i; simp
  rw [hc]
  rfl

private theorem cut_submodular {n : ℕ} (x : Sym2 (Fin (n + 1)) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (S T : Finset (Fin (n + 1))) :
    cut x T - cut x (S ∪ T) ≥ cut x (S ∩ T) - cut x S := by
  classical
  have h : cut x (S ∩ T) + cut x (S ∪ T) ≤ cut x S + cut x T := by
    simp only [cut_formula, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    by_cases his : i ∈ S <;> by_cases hit : i ∈ T <;>
      by_cases hjs : j ∈ S <;> by_cases hjt : j ∈ T <;>
      simp [his, hit, hjs, hjt, hx]
  linarith

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


private lemma crossing_general {n : ℕ} (x : Sym2 (Fin (n+1)) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (ρ : Finset (Fin (n+1)) → ℕ) (S T : Finset (Fin (n+1)))
    (hρ : ρ T ≤ ρ (S ∪ T)) (hS : cut x S ≤ 2)
    (hR : ∀ R : Finset (Fin (n+1)), R ⊆ S → R.Nonempty → R ≠ S → 2 ≤ cut x R)
    (hint : (S ∩ T).Nonempty) (hne : ¬ S ⊆ T) :
    violation x ρ T ≤ violation x ρ (S ∪ T) := by
  have hproper : S ∩ T ≠ S := by
    intro h
    apply hne
    rw [← h]
    exact Finset.inter_subset_right
  have hc := hR (S ∩ T) Finset.inter_subset_left hint hproper
  have hs := cut_submodular x hx S T
  have hr : (ρ T : ℝ) ≤ ρ (S ∪ T) := Nat.cast_le.mpr hρ
  unfold violation
  linarith

private lemma safe_general {n : ℕ} (x : Sym2 (Fin (n+1)) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (ρ : Finset (Fin (n+1)) → ℕ) (S : Finset (Fin (n+1)))
    (hρ : ∀ T, (0 : Fin (n+1)) ∉ T → ρ T ≤ ρ (S ∪ T))
    (hS0 : (0 : Fin (n+1)) ∉ S) (hS : cut x S ≤ 2)
    (hR : ∀ R : Finset (Fin (n+1)), R ⊆ S → R.Nonempty → R ≠ S → 2 ≤ cut x R) :
    SafeToShrink x ρ S := by
  intro T hT hcard hv
  by_cases hST : S ⊆ T
  · exact ⟨T, hT, hcard, Or.inl hST, le_rfl⟩
  by_cases hd : Disjoint S T
  · exact ⟨T, hT, hcard, Or.inr hd, le_rfl⟩
  refine ⟨S ∪ T, by simp [hS0,hT], le_trans hcard (Finset.card_le_card Finset.subset_union_right),
    Or.inl Finset.subset_union_left, ?_⟩
  apply crossing_general x hx ρ S T (hρ T hT) hS hR ?_ hST
  exact Finset.not_disjoint_iff_nonempty_inter.mp hd

theorem solution {n : ℕ} (q : Fin (n + 1) → ℕ) (Q : ℝ) (hQ : 0 < Q)
    (hq : ∀ i : Fin (n + 1), i ≠ 0 → 0 < q i ∧ (q i : ℝ) ≤ Q)
    (x : Sym2 (Fin (n + 1)) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (S : Finset (Fin (n + 1))) (hS0 : (0 : Fin (n + 1)) ∉ S) (hS : cut x S ≤ 2)
    (hR : ∀ R : Finset (Fin (n + 1)), R ⊆ S → R.Nonempty → R ≠ S → 2 ≤ cut x R)
    (T : Finset (Fin (n + 1))) (hT0 : (0 : Fin (n + 1)) ∉ T)
    (hTS : (T ∩ S).Nonempty) (hTmS : (T \ S).Nonempty) (hSmT : (S \ T).Nonempty) :
    violation x (binPackingNumber q Q) T ≤ violation x (binPackingNumber q Q) (S ∪ T) := by
  apply crossing_general x hx (binPackingNumber q Q) S T ?_ hS hR
    (by simpa [Finset.inter_comm] using hTS) ?_
  · apply packing_mono q Q hQ.le T (S ∪ T) Finset.subset_union_right
    intro i hi
    apply (hq i ?_).2
    rintro rfl
    simp [hS0,hT0] at hi
  · intro hST
    obtain ⟨i, hi⟩ := hSmT
    exact (Finset.mem_sdiff.mp hi).2 (hST (Finset.mem_sdiff.mp hi).1)
