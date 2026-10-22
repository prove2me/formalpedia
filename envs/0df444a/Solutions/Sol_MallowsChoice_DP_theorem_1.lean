-- Prove2me | solution 1 for MallowsChoice.DP.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T02:04:46.761905+00:00
-- url     : https://prove2.me/submissions/5e218380-4eb4-4dcf-a230-78038c547710

import Mathlib
import Definitions.Def_MallowsChoice_DP_Setting
import Theorems.Thm_MallowsChoice_DP_pi_sum_eq_choiceProb
import Theorems.Thm_MallowsChoice_DP_case_1
import Theorems.Thm_MallowsChoice_DP_case_2_old
import Theorems.Thm_MallowsChoice_DP_case_2_new

open Finset MallowsChoice.DP

theorem solution (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ)
    (S : Finset (Fin n)) (h1 : (⟨0, hn⟩ : Fin n) ∈ S) :
    (∀ a ∈ S, choiceProb θ S a =
      ∑ s ∈ Icc 1 n, piDP θ S (a.val + 1) s n) ∧
    (∀ a ∉ S, (∑ s ∈ Icc 1 n, piDP θ S (a.val + 1) s n) = 0) := by
  -- out-of-range entries of the probabilistic table vanish
  have hout : ∀ m, m ≤ n → ∀ i s, ¬ (1 ≤ i ∧ i ≤ m ∧ 1 ≤ s ∧ s ≤ m) →
      piProb θ S i s m = 0 := by
    intro m hm i s h
    unfold piProb
    rw [dif_pos hm]
    by_cases hi : 1 ≤ i ∧ i ≤ m
    · rw [dif_pos hi, dif_neg (by omega)]
    · rw [dif_neg hi]
  -- base case m = 1
  have hbase : ∀ i s, piDP θ S i s 1 = piProb θ S i s 1 := by
    intro i s
    have hdp : piDP θ S i s 1 = if 1 ≤ n ∧ i = 1 ∧ s = 1 then 1 else 0 := by
      simp only [piDP, piDPAux]; simp
    rw [hdp]
    by_cases his : i = 1 ∧ s = 1
    · obtain ⟨rfl, rfl⟩ := his
      rw [if_pos ⟨hn, rfl, rfl⟩]
      unfold piProb
      rw [dif_pos hn, dif_pos ⟨le_rfl, le_rfl⟩, dif_pos ⟨le_rfl, le_rfl⟩]
      have hr : ∀ σ : Equiv.Perm (Fin 1), rimProb θ 1 σ = 1 := by
        intro σ
        simp only [rimProb, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
        rw [Fintype.sum_subsingleton _ (1 : Equiv.Perm (Fin 0)),
          if_pos (fun j => Subsingleton.elim (α := Fin 1) _ _)]
        simp [alpha]
      simp only [hr, one_mul]
      rw [Fintype.sum_unique]
      rw [if_pos]
      refine ⟨?_, ?_, ?_⟩
      · convert h1 using 1
        ext; simp
      · have := (default : Equiv.Perm (Fin 1)) ⟨0, by omega⟩
        simp [Fin.fin_one_eq_zero]
      · intro b _ hb
        exact absurd (Subsingleton.elim _ _) hb
    · rw [if_neg (by tauto)]
      rw [hout 1 hn i s (by omega)]
  -- inductive step
  have hstep : ∀ m, 1 ≤ m → m < n →
      (∀ i s, piDP θ S i s m = piProb θ S i s m) →
      ∀ i s, piDP θ S i s (m + 1) = piProb θ S i s (m + 1) := by
    intro m hm hmn ih i s
    have hm0 : m ≠ 0 := by omega
    have hunf : piDP θ S i s (m + 1) =
        if 1 ≤ i ∧ i ≤ m + 1 ∧ 1 ≤ s ∧ s ≤ m + 1 then
          if i ≤ m then
            (1 - gamma θ s (m + 1)) * piDP θ S i s m +
              (if (⟨m, hmn⟩ : Fin n) ∈ S then (0 : ℝ) else 1) *
                gamma θ (s - 1) (m + 1) * piDP θ S i (s - 1) m
          else
            (if (⟨m, hmn⟩ : Fin n) ∈ S then (1 : ℝ) else 0) *
              alpha θ s (m + 1) *
                ∑ j ∈ Icc 1 m, ∑ ℓ ∈ Icc s n, piDP θ S j ℓ m
        else 0 := by
      simp only [piDP]
      rw [piDPAux, if_neg hm0, dif_pos hmn]
    rw [hunf]
    by_cases hr : 1 ≤ i ∧ i ≤ m + 1 ∧ 1 ≤ s ∧ s ≤ m + 1
    · rw [if_pos hr]
      by_cases him : i ≤ m
      · rw [if_pos him, ih, ih]
        by_cases hS : (⟨m, hmn⟩ : Fin n) ∈ S
        · rw [if_pos hS, case_2_old n θ hθ S m hm hmn hS i hr.1 him s hr.2.2.1 hr.2.2.2]
          ring
        · rw [if_neg hS, (case_1 n θ hθ S m hm hmn hS).2 i hr.1 him s hr.2.2.1 hr.2.2.2]
          ring
      · rw [if_neg him]
        have hi : i = m + 1 := by omega
        subst hi
        by_cases hS : (⟨m, hmn⟩ : Fin n) ∈ S
        · rw [if_pos hS, case_2_new n hn θ hθ S h1 m hm hmn hS s hr.2.2.1 hr.2.2.2]
          simp only [ih, one_mul]
        · rw [if_neg hS, (case_1 n θ hθ S m hm hmn hS).1 s]
          ring
    · rw [if_neg hr, hout (m + 1) hmn i s (by omega)]
  have hall : ∀ m, 1 ≤ m → m ≤ n → ∀ i s, piDP θ S i s m = piProb θ S i s m := by
    intro m hm hmn
    induction m, hm using Nat.le_induction with
    | base => exact hbase
    | succ m hm ihm => exact hstep m hm (by omega) (ihm (by omega))
  refine ⟨?_, ?_⟩
  · intro a ha
    rw [pi_sum_eq_choiceProb n θ hθ S a ha]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hall n hn le_rfl]
  · intro a ha
    refine Finset.sum_eq_zero (fun s _ => ?_)
    rw [hall n hn le_rfl]
    unfold piProb
    rw [dif_pos le_rfl]
    split_ifs with h2 h3
    · refine Finset.sum_eq_zero (fun σ _ => ?_)
      rw [if_neg]
      · simp
      · rintro ⟨hmem, -⟩
        apply ha
        convert hmem using 1
        ext; simp
    · rfl
    · rfl
