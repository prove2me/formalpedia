-- Prove2me | solution 1 for GreedyRegionGrowing.Layouts.Supplement.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:12:44.32997+00:00
-- url     : https://prove2.me/submissions/4949f529-0e41-4143-9485-7afbc83ffc13

import Mathlib
import Definitions.Def_GreedyRegionGrowing_Layouts_Foundation

noncomputable section
open Finset QAlgorithms.Complexity
attribute [local instance] Classical.propDecidable

theorem solution (κ L : ℕ) (D : ℝ) (a : ℕ → ℝ) (F : ℕ → ℝ → ℝ)
    (t : Fin L → ℕ) (hκ : L+1 ≤ κ)
    (ha : ∀ i j, i < j → j ≤ κ → a j < a i)
    (hF : ∀ t, Antitone (F t)) (ht : Monotone t)
    (hinc : ∀ t r, F t r ≤ F (t+1) r)
    (hval : ∀ t r, 1 ≤ F t r ∧ F t r ≤ D) :
  ((univ.filter (fun i : Fin L => F (t i) (a (i.val+1)) >
    2*F (t i) (a i.val))).card : ℝ) ≤ Real.logb 2 D := by
  have hD : 1 ≤ D := le_trans (hval 0 0).1 (hval 0 0).2
  have hmonoT : ∀ s s' : ℕ, s ≤ s' → ∀ r, F s r ≤ F s' r := by
    intro s s' hss r
    induction s', hss using Nat.le_induction with
    | base => exact le_rfl
    | succ n _ ih => exact ih.trans (hinc n r)
  set p : Fin L → Prop := fun i => F (t i) (a (i.val+1)) > 2*F (t i) (a i.val) with hp
  -- y_i ≥ g_i
  have hyg : ∀ i : Fin L, F (t i) (a i.val) ≤ F (t i) (a (i.val+1)) := by
    intro i
    apply hF
    exact le_of_lt (ha i.val (i.val+1) (Nat.lt_succ_self _) (by omega))
  have key : ∀ k (hk : k < L),
      (2:ℝ) ^ (univ.filter (fun i : Fin L => i.val ≤ k ∧ p i)).card
        ≤ F (t ⟨k, hk⟩) (a (k+1)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hg1 := (hval (t ⟨0, hk⟩) (a 0)).1
      have hy := hyg ⟨0, hk⟩
      by_cases h0 : p ⟨0, hk⟩
      · have hsub : univ.filter (fun i : Fin L => i.val ≤ 0 ∧ p i) ⊆ {⟨0, hk⟩} := by
          intro i hi
          simp only [mem_filter] at hi
          simp only [mem_singleton]; ext; simp; omega
        have hc := card_le_card hsub
        rw [card_singleton] at hc
        have : (2:ℝ) ^ (univ.filter (fun i : Fin L => i.val ≤ 0 ∧ p i)).card ≤ 2 ^ 1 :=
          pow_le_pow_right₀ (by norm_num) hc
        have h0' : F (t ⟨0, hk⟩) (a (0+1)) > 2*F (t ⟨0, hk⟩) (a 0) := h0
        simp only [pow_one] at this
        simp only [Nat.zero_add] at h0' ⊢
        linarith
      · have hemp : univ.filter (fun i : Fin L => i.val ≤ 0 ∧ p i) = ∅ := by
          apply filter_false_of_mem
          rintro i - ⟨hi, hpi⟩
          have : i = ⟨0, hk⟩ := by ext; simp; omega
          exact h0 (this ▸ hpi)
        rw [hemp, card_empty, pow_zero]
        simp only [Nat.zero_add]
        linarith
    | succ k ih =>
      intro hk
      have ihk := ih (by omega)
      -- g(k+1) ≥ y_k
      have hstep : F (t ⟨k, by omega⟩) (a (k+1)) ≤ F (t ⟨k+1, hk⟩) (a (k+1)) :=
        hmonoT _ _ (ht (by simp [Fin.le_def])) _
      have hy := hyg ⟨k+1, hk⟩
      have hunion : univ.filter (fun i : Fin L => i.val ≤ k+1 ∧ p i) ⊆
          univ.filter (fun i : Fin L => i.val ≤ k ∧ p i) ∪
          univ.filter (fun i : Fin L => i.val = k+1 ∧ p i) := by
        intro i hi
        simp only [mem_filter, mem_univ, true_and, mem_union] at hi ⊢
        obtain ⟨h1, h2⟩ := hi
        by_cases hik : i.val ≤ k
        · exact Or.inl ⟨hik, h2⟩
        · exact Or.inr ⟨by omega, h2⟩
      have hc := (card_le_card hunion).trans (card_union_le _ _)
      by_cases hk1 : p ⟨k+1, hk⟩
      · have hsub : univ.filter (fun i : Fin L => i.val = k+1 ∧ p i) ⊆ {⟨k+1, hk⟩} := by
          intro i hi
          simp only [mem_filter] at hi
          simp only [mem_singleton]; ext; simp; omega
        have hc2 := card_le_card hsub
        rw [card_singleton] at hc2
        have : (2:ℝ) ^ (univ.filter (fun i : Fin L => i.val ≤ k+1 ∧ p i)).card ≤
            2 ^ ((univ.filter (fun i : Fin L => i.val ≤ k ∧ p i)).card + 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        rw [pow_succ] at this
        have h' : F (t ⟨k+1, hk⟩) (a (k+1+1)) > 2*F (t ⟨k+1, hk⟩) (a (k+1)) := hk1
        nlinarith
      · have hemp : univ.filter (fun i : Fin L => i.val = k+1 ∧ p i) = ∅ := by
          apply filter_false_of_mem
          rintro i - ⟨hi, hpi⟩
          have : i = ⟨k+1, hk⟩ := by ext; simp; omega
          exact hk1 (this ▸ hpi)
        rw [hemp, card_empty, Nat.add_zero] at hc
        have : (2:ℝ) ^ (univ.filter (fun i : Fin L => i.val ≤ k+1 ∧ p i)).card ≤
            2 ^ ((univ.filter (fun i : Fin L => i.val ≤ k ∧ p i)).card) :=
          pow_le_pow_right₀ (by norm_num) hc
        linarith
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    simp
    exact Real.logb_nonneg (by norm_num) hD
  · have hk := key (L-1) (by omega)
    have heq : univ.filter (fun i : Fin L => i.val ≤ L-1 ∧ p i) = univ.filter p := by
      apply filter_congr
      intro i _
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨by omega, h⟩
    rw [heq] at hk
    have hle : (2:ℝ) ^ (univ.filter p).card ≤ D := hk.trans (hval _ _).2
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_natCast]
    exact hle
