-- Prove2me | solution 1 for MultiServerAppt.waiting_time_hitting_time
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:14:31.852773+00:00
-- url     : https://prove2.me/submissions/e078c7f7-9aa3-4759-a97c-9be176882223

import Mathlib
import Definitions.Def_MultiServerAppt_W
import Definitions.Def_MultiServerAppt_Y

namespace MultiServerAppt.Aux_MS

open MultiServerAppt

/-- If `(W, ∞) ⊆ A ⊆ [W, ∞)` then `sInf A = W`. -/
theorem sInf_eq_of_sandwich (A : Set ℝ) (W : ℝ) (h1 : ∀ t, W < t → t ∈ A)
    (h2 : ∀ t ∈ A, W ≤ t) : sInf A = W := by
  have hne : A.Nonempty := ⟨W + 1, h1 _ (by linarith)⟩
  have hbdd : BddBelow A := ⟨W, h2⟩
  apply le_antisymm
  · apply le_of_forall_pos_lt_add
    intro ε hε
    exact lt_of_le_of_lt (csInf_le hbdd (h1 (W + ε / 2) (by linarith))) (by linarith)
  · exact le_csInf hne h2

end MultiServerAppt.Aux_MS

open MultiServerAppt MultiServerAppt.Aux_MS in
theorem solution (s c : ℕ) (x b : ℕ → ℝ) (hs : 1 ≤ s)
    (hb : ∀ d, 0 ≤ b d) :
    W s x b c = sInf {t : ℝ | 0 ≤ t ∧ Y s x b c t ≤ s} ∧
    W s x b c = sInf {t : ℝ | 0 ≤ t ∧ Y s x b (c - 1) (t + x c) < s} := by
  classical
  by_cases hcs : c ≤ s
  · -- trivial case
    have harr : arr s x c = 0 := by
      unfold arr
      rw [show c - s = 0 by omega]
      simp
    have hW : W s x b c = 0 := by
      unfold W
      rw [harr]
      unfold start
      rw [if_pos hcs]
      ring
    rw [hW]
    have hYc : ∀ t, Y s x b c t ≤ s := by
      intro t
      unfold Y
      calc ((Finset.Icc 1 c).filter _).card ≤ (Finset.Icc 1 c).card := Finset.card_filter_le _ _
        _ = c := by simp
        _ ≤ s := hcs
    have hYc1 : ∀ u, Y s x b (c - 1) u < s := by
      intro u
      unfold Y
      calc ((Finset.Icc 1 (c - 1)).filter _).card ≤ (Finset.Icc 1 (c - 1)).card :=
            Finset.card_filter_le _ _
        _ = c - 1 := by simp
        _ < s := by omega
    constructor
    · symm
      apply sInf_eq_of_sandwich
      · intro t ht; exact ⟨ht.le, hYc t⟩
      · intro t ht; exact ht.1
    · symm
      apply sInf_eq_of_sandwich
      · intro t ht; exact ⟨ht.le, hYc1 _⟩
      · intro t ht; exact ht.1
  · push_neg at hcs
    -- the counting function on earlier customers
    set g : ℝ → ℕ := fun τ => ((Finset.Icc 1 (c - 1)).filter (fun d => τ < dep s x b d)).card
      with hg
    have hgdef : ∀ τ, ((Finset.Icc 1 (c - 1)).attach.filter
        (fun d => τ < start s x b d.1 + b d.1)).card = g τ := by
      intro τ
      show _ = ((Finset.Icc 1 (c - 1)).filter (fun d => τ < dep s x b d)).card
      rw [Finset.card_filter, Finset.card_filter]
      unfold dep
      exact Finset.sum_attach (Finset.Icc 1 (c - 1))
        (fun d => if τ < start s x b d + b d then 1 else 0)
    set S : Set ℝ := {τ | g τ < s} with hS
    have hstart : start s x b c = max (arr s x c) (sInf S) := by
      rw [start, if_neg (not_le.mpr hcs)]
      congr 1
      congr 1
      ext τ
      simp only [Set.mem_setOf_eq, hS]
      rw [hgdef]
    have hgmono : ∀ τ₁ τ₂, τ₁ ≤ τ₂ → g τ₂ ≤ g τ₁ := by
      intro τ₁ τ₂ h
      apply Finset.card_le_card
      intro d hd
      simp only [Finset.mem_filter] at hd ⊢
      exact ⟨hd.1, lt_of_le_of_lt h hd.2⟩
    set M : ℝ := ∑ d ∈ Finset.Icc 1 (c - 1), |dep s x b d| with hM
    have hdepM : ∀ d ∈ Finset.Icc 1 (c - 1), |dep s x b d| ≤ M := fun d hd =>
      Finset.single_le_sum (f := fun d => |dep s x b d|) (fun _ _ => abs_nonneg _) hd
    have hSne : S.Nonempty := by
      refine ⟨M, ?_⟩
      simp only [hS, Set.mem_setOf_eq, hg]
      have : (Finset.Icc 1 (c - 1)).filter (fun d => M < dep s x b d) = ∅ := by
        apply Finset.filter_false_of_mem
        intro d hd
        have := hdepM d hd
        have := le_abs_self (dep s x b d)
        linarith
      rw [this]; simp; omega
    have hSbdd : BddBelow S := by
      refine ⟨-M, fun τ hτ => ?_⟩
      by_contra hlt
      push_neg at hlt
      simp only [hS, Set.mem_setOf_eq, hg] at hτ
      have : (Finset.Icc 1 (c - 1)).filter (fun d => τ < dep s x b d) = Finset.Icc 1 (c - 1) := by
        apply Finset.filter_true_of_mem
        intro d hd
        have := hdepM d hd
        have := neg_abs_le (dep s x b d)
        linarith
      rw [this] at hτ
      simp at hτ
      omega
    set τs := sInf S with hτs
    have hmemS : ∀ τ, τs < τ → g τ < s := by
      intro τ hτ
      obtain ⟨τ', hτ'S, hτ'lt⟩ := exists_lt_of_csInf_lt hSne hτ
      exact lt_of_le_of_lt (hgmono _ _ hτ'lt.le) hτ'S
    have hnotS : ∀ τ, τ < τs → s ≤ g τ := by
      intro τ hτ
      by_contra h
      push_neg at h
      have := csInf_le hSbdd (show τ ∈ S from h)
      linarith
    -- the waiting time
    have hW : W s x b c = max 0 (τs - arr s x c) := by
      unfold W
      rw [hstart]
      rcases le_total (arr s x c) τs with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]
      · rw [max_eq_left h, max_eq_left (by linarith)]; ring
    have hW0 : 0 ≤ W s x b c := by rw [hW]; exact le_max_left _ _
    have hdepc : dep s x b c = arr s x c + W s x b c + b c := by
      unfold dep W; ring
    -- Y in terms of g
    have hY : ∀ t, Y s x b c t = g (arr s x c + t) +
        (if arr s x c + t < dep s x b c then 1 else 0) := by
      intro t
      unfold Y
      rw [hg]
      simp only
      rw [Finset.card_filter, Finset.card_filter]
      have hc : c = (c - 1) + 1 := by omega
      conv_lhs => rw [hc]
      rw [Finset.sum_Icc_succ_top (by omega), ← hc]
    have harr : arr s x c = arr s x (c - 1) + x c := by
      unfold arr
      rw [show c - s = (c - 1 - s) + 1 by omega, Finset.sum_Icc_succ_top (by omega)]
      congr 2
      omega
    have hY1 : ∀ t, Y s x b (c - 1) (t + x c) = g (arr s x c + t) := by
      intro t
      unfold Y
      rw [hg, harr]
      congr 1
      apply Finset.filter_congr
      intro d _
      constructor <;> intro h <;> linarith
    constructor
    · symm
      apply sInf_eq_of_sandwich
      · intro t ht
        refine ⟨by linarith, ?_⟩
        rw [hY]
        have h1 : τs < arr s x c + t := by
          rw [hW] at ht
          have := le_max_right 0 (τs - arr s x c)
          linarith
        have h2 := hmemS _ h1
        split_ifs <;> omega
      · rintro t ⟨ht0, htY⟩
        by_contra hlt
        push_neg at hlt
        have hWpos : 0 < W s x b c := lt_of_le_of_lt ht0 hlt
        have h1 : arr s x c + t < τs := by
          rw [hW] at hlt hWpos
          rcases le_total 0 (τs - arr s x c) with h | h
          · rw [max_eq_right h] at hlt; linarith
          · rw [max_eq_left h] at hlt; linarith
        have h2 := hnotS _ h1
        rw [hY] at htY
        have h3 : arr s x c + t < dep s x b c := by
          rw [hdepc]; linarith [hb c]
        rw [if_pos h3] at htY
        omega
    · symm
      apply sInf_eq_of_sandwich
      · intro t ht
        refine ⟨by linarith, ?_⟩
        rw [hY1]
        apply hmemS
        rw [hW] at ht
        have := le_max_right 0 (τs - arr s x c)
        linarith
      · rintro t ⟨ht0, htY⟩
        by_contra hlt
        push_neg at hlt
        have h1 : arr s x c + t < τs := by
          rw [hW] at hlt
          rcases le_total 0 (τs - arr s x c) with h | h
          · rw [max_eq_right h] at hlt; linarith
          · rw [max_eq_left h] at hlt; linarith
        have h2 := hnotS _ h1
        rw [hY1] at htY
        omega
