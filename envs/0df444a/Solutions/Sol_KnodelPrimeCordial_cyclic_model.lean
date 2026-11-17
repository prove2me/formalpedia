-- Prove2me | solution 1 for KnodelPrimeCordial.cyclic_model
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T08:19:57.555509+00:00
-- url     : https://prove2.me/submissions/ff06dd61-9f77-4356-97eb-8cfcb1050d10

import Theorems.Thm_KnodelPrimeCordial_vtx_cycle_edge
import Theorems.Thm_KnodelPrimeCordial_vtx_adj_off_cycle
open KnodelPrimeCordial
private theorem vtx_bijective (n : ℕ) (hn : Even n) (h8 : 8 ≤ n) :
    Function.Bijective (vtx n (by omega)) := by
  have hn2 : n = 2 * (n / 2) := by rcases hn with ⟨k, hk⟩; omega
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    simp only [vtx] at hab
    split_ifs at hab with ha2 hb2 hb2
    · have h := congrArg (fun p => (p.2 : ℕ)) hab
      simp only at h
      have ham : a.val / 2 < n / 2 := by omega
      have hbm : b.val / 2 < n / 2 := by omega
      rw [Nat.mod_eq_of_lt ham, Nat.mod_eq_of_lt hbm] at h
      apply Fin.ext
      omega
    · have h := congrArg (fun p => (p.1 : ℕ)) hab
      simp at h
    · have h := congrArg (fun p => (p.1 : ℕ)) hab
      simp at h
    · have h := congrArg (fun p => (p.2 : ℕ)) hab
      simp only at h
      have ham : (a.val + 1) / 2 ≤ n / 2 := by omega
      have hbm : (b.val + 1) / 2 ≤ n / 2 := by omega
      by_cases haend : (a.val + 1) / 2 = n / 2 <;>
        by_cases hbend : (b.val + 1) / 2 = n / 2
      · apply Fin.ext; omega
      · rw [haend, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at h
        omega
      · rw [hbend, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at h
        omega
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
        apply Fin.ext; omega
  · simp only [Fintype.card_fin, Fintype.card_prod]
    omega


theorem solution (n : ℕ) (hn : Even n) (h8 : 8 ≤ n) :
    Function.Bijective (vtx n (by omega)) ∧
      ∀ a b : Fin n, (cyc n).Adj a b ↔
        (knodel 3 n).Adj (vtx n (by omega) a) (vtx n (by omega) b) := by
  refine ⟨vtx_bijective n hn h8, ?_⟩
  intro a b
  by_cases hab : b.val = (a.val + 1) % n
  · have hedge := vtx_cycle_edge n hn h8 a b hab
    have hne : a ≠ b := by
      intro heq
      subst b
      exact (knodel 3 n).loopless.irrefl _ hedge
    exact iff_of_true ⟨hne, Or.inl hab⟩ hedge
  by_cases hba : a.val = (b.val + 1) % n
  · have hedge := (vtx_cycle_edge n hn h8 b a hba).symm
    have hne : a ≠ b := by
      intro heq
      subst b
      exact (knodel 3 n).loopless.irrefl _ hedge
    exact iff_of_true ⟨hne, Or.inr (Or.inl hba)⟩ hedge
  rw [vtx_adj_off_cycle n hn h8 a b hab hba]
  change (a ≠ b ∧ (_ ∨ _ ∨ _ ∨ _)) ↔ _
  simp only [hab, hba, false_or]
