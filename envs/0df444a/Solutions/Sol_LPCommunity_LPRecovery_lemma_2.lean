-- Prove2me | solution 1 for LPCommunity.LPRecovery.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:37:25.600253+00:00
-- url     : https://prove2.me/submissions/3b6abb74-eda6-462c-ade3-759ed2d7b863

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting

set_option autoImplicit false
open Finset
open scoped Classical
open LPCommunity.LPRecovery

theorem lpBounds {n : ℕ} {x : Fin n → Fin n → ℝ} (hx : LPCommunity.LPRecovery.LPFeasible n x)
    (i j : Fin n) (hij : i < j) : 0 ≤ x i j ∧ x i j ≤ 1 := by
  obtain ⟨hsymm, hdiag, h1, h2, h3⟩ := hx
  by_cases hn : 3 ≤ n
  · have hk : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, j} := by
        intro k _
        by_cases hki : k = i
        · simp [hki]
        · simp [hcon k hki]
      have h := Finset.card_le_card hsub
      have h' : ({i, j} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
      rw [Finset.card_univ, Fintype.card_fin] at h
      omega
    obtain ⟨k, hki, hkj⟩ := hk
    have hij' : i ≠ j := ne_of_lt hij
    have tri : ∀ a b c : Fin n, a ≠ b → c ≠ a → c ≠ b → x a b ≤ x a c + x b c := by
      intro a b c hab hca hcb
      rcases lt_or_gt_of_ne hab with h | h
      · exact h1 a b c h hca hcb
      · have := h1 b a c h hcb hca
        rw [hsymm a b]
        linarith
    have t1 := tri i k j hki.symm hij'.symm hkj.symm
    have t2 := tri j k i hkj.symm hij' hki.symm
    have t3 := tri i j k hij' hki hkj
    have hs : x i j + x i k + x j k ≤ 2 := by
      rcases lt_or_gt_of_ne hki with h | h
      · have := h2 k i j h hij
        linarith [hsymm k i, hsymm k j]
      · rcases lt_or_gt_of_ne hkj with h' | h'
        · have := h2 i k j h h'
          linarith [hsymm k j]
        · have := h2 i j k hij h'
          linarith
    constructor
    · linarith [hsymm k j, hsymm j i, hsymm k i]
    · linarith
  · have hj := j.isLt
    have hij2 : i.val < j.val := hij
    obtain rfl : n = 2 := by omega
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    simp [Fin.sum_univ_two] at h3
    constructor <;> linarith

theorem solution {n : ℕ} (G G' : SimpleGraph (Fin n)) (V1 : Finset (Fin n))
    (hV1 : LPCommunity.MinBisect.IsBisection n V1) (hrec : LPRecovers G V1)
    (hsame : ∀ i j, LPCommunity.MinBisect.sameSide V1 i j → (G'.Adj i j ↔ G.Adj i j))
    (hcross : ∀ i j, ¬ LPCommunity.MinBisect.sameSide V1 i j → G'.Adj i j → G.Adj i j) :
    LPRecovers G' V1 := by
  obtain ⟨⟨hfeas, hopt⟩, huniq⟩ := hrec
  have hGG : ∀ i j, G'.Adj i j → G.Adj i j := by
    intro i j h
    by_cases hs : LPCommunity.MinBisect.sameSide V1 i j
    · exact (hsame i j hs).1 h
    · exact hcross i j hs h
  set d : (Fin n → Fin n → ℝ) → ℝ := fun y =>
    ∑ i, ∑ j, if (i < j ∧ G.Adj i j ∧ ¬ G'.Adj i j) then y i j else 0 with hd
  have hdiff : ∀ y, lpObj G y - lpObj G' y = d y := by
    intro y
    unfold lpObj
    rw [hd]
    simp only
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h1 : i < j
    · by_cases h2 : G.Adj i j
      · by_cases h3 : G'.Adj i j <;> simp [h1, h2, h3]
      · have h3 : ¬ G'.Adj i j := fun h => h2 (hGG i j h)
        simp [h1, h2, h3]
    · simp [h1]
  have hdle : ∀ z, LPFeasible n z → d z ≤ d (cutVec V1) := by
    intro z hz
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hc : (i < j ∧ G.Adj i j ∧ ¬ G'.Adj i j)
    · rw [if_pos hc, if_pos hc]
      have hns : ¬ LPCommunity.MinBisect.sameSide V1 i j := by
        intro hs
        exact hc.2.2 ((hsame i j hs).2 hc.2.1)
      have : cutVec V1 i j = 1 := by simp [cutVec, hns]
      rw [this]
      exact (lpBounds hz i j hc.1).2
    · rw [if_neg hc, if_neg hc]
  have hcopt : LPOptimal G' (cutVec V1) := by
    refine ⟨hfeas, fun z hz => ?_⟩
    have h1 := hopt z hz
    have h2 := hdle z hz
    have e1 := hdiff (cutVec V1)
    have e2 := hdiff z
    linarith
  refine ⟨hcopt, fun y hy => ?_⟩
  apply huniq
  refine ⟨hy.1, fun z hz => ?_⟩
  have h1 := hy.2 (cutVec V1) hfeas
  have h2 := hdle y hy.1
  have h3 := hopt z hz
  have e1 := hdiff (cutVec V1)
  have e2 := hdiff y
  have h4 := hopt y hy.1
  linarith
