-- Prove2me | solution 1 for HubSpokePricing.Lagrangian.proposition_B_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:16:27.517408+00:00
-- url     : https://prove2.me/submissions/ca1c0c54-4761-4741-9c25-79f5691d243d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Model
import Definitions.Def_HubSpokePricing_Lagrangian_Prob
import Theorems.Thm_HubSpokePricing_Lagrangian_proposition_3_3
import Theorems.Thm_HubSpokePricing_Lagrangian_lemma_B_1_support

open HubSpokePricing.Lagrangian Finset

theorem solution (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam)
    (i : Fin N.n) (s : SpokeSol N.m) (hs : SpokeOptimal N lam i s) :
    IsLogConcave s.pN := by
  obtain ⟨hsupp, hirr⟩ := lemma_B_1_support N hN lam hlam i s hs
  have hmono := proposition_3_3 N hN lam hlam i s hs
  obtain ⟨hp0, hp1, hdo, hdi, hflow, -, -⟩ := hs.1
  have hqo := hN.2.1 i
  have hqi := hN.2.2.1 i
  -- natural-number readings
  have ePN : ∀ k (hk : k ≤ N.m), s.pN k = s.p ⟨k, by omega⟩ := by
    intro k hk; unfold SpokeSol.pN; rw [dif_pos hk]
  have ePNz : ∀ k, N.m < k → s.pN k = 0 := by
    intro k hk; unfold SpokeSol.pN; rw [dif_neg (by omega)]
  have hpN0 : ∀ k, 0 ≤ s.pN k := by
    intro k
    by_cases hk : k ≤ N.m
    · rw [ePN k hk]; exact hp0 _
    · rw [ePNz k (by omega)]
  -- positivity of `pN k` means `k ≤ top` (and `k ≤ m`)
  have hpos_iff : ∀ k (hk : k ≤ N.m), 0 < s.pN k ↔ k ≤ s.top := by
    intro k hk; rw [ePN k hk]; exact hsupp ⟨k, by omega⟩
  have hpos_le : ∀ k, 0 < s.pN k → k ≤ N.m := by
    intro k hk
    by_contra h
    rw [ePNz k (by omega)] at hk; exact lt_irrefl _ hk
  refine ⟨hpN0, ?_, ?_, ?_⟩
  · -- total mass one
    have : ∑ k ∈ range (N.m + 1), s.pN k = 1 := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => s.pN k)]
      rw [← hp1]
      apply sum_congr rfl; intro x _
      rw [ePN x (Nat.lt_succ_iff.mp x.2)]
    rw [← this]
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    simp at hk
    exact ePNz k (by omega)
  · -- support is an interval
    intro a b k hak hkb ha hb
    have hbm := hpos_le b hb
    have hbt := (hpos_iff b hbm).1 hb
    exact (hpos_iff k (by omega)).2 (by omega)
  · -- ratio inequality
    intro k hk1
    rcases (hpN0 (k - 1)).lt_or_eq with ha | ha
    · rcases (hpN0 (k + 1)).lt_or_eq with hc | hc
      · have hcm := hpos_le (k + 1) hc
        have hct := (hpos_iff (k + 1) hcm).1 hc
        have hb : 0 < s.pN k := (hpos_iff k (by omega)).2 (by omega)
        -- flow balance at `k - 1` and at `k`
        have fl1 := hflow ⟨k - 1, by omega⟩
        have fl2 := hflow ⟨k, by omega⟩
        have ir1 := hirr ⟨k - 1, by omega⟩
        have ir2 := hirr ⟨k, by omega⟩
        have mo := hmono ⟨k, by omega⟩ ⟨k + 1, by omega⟩ (by simp only [Fin.mk_le_mk]; omega)
        have mo' := hmono ⟨k - 1, by omega⟩ ⟨k, by omega⟩ (by simp only [Fin.mk_le_mk]; omega)
        simp only [Fin.castSucc_mk, Fin.succ_mk] at fl1 fl2 ir1 ir2
        rw [ePN (k - 1) (by omega)] at ha
        rw [ePN (k + 1) hcm] at hc
        rw [ePN k (by omega)] at hb
        have e1 : k - 1 + 1 = k := by omega
        simp only [e1] at fl1 ir1
        obtain ⟨hdIn1, hdOut1⟩ := ir1 hb
        obtain ⟨hdIn2, hdOut2⟩ := ir2 hc
        obtain ⟨mo1, -⟩ := mo hb hc
        obtain ⟨-, mo2⟩ := mo' ha hb
        rw [ePN (k - 1) (by omega), ePN (k + 1) hcm, ePN k (by omega)]
        set a := s.p ⟨k - 1, by omega⟩
        set b := s.p ⟨k, by omega⟩
        set c := s.p ⟨k + 1, by omega⟩
        set DI1 := s.dIn ⟨k - 1, by omega⟩
        set DI2 := s.dIn ⟨k, by omega⟩
        set DO1 := s.dOut ⟨k, by omega⟩
        set DO2 := s.dOut ⟨k + 1, by omega⟩
        -- a qIn DI1 = b qOut DO1,  b qIn DI2 = c qOut DO2
        have hK : 0 < N.qIn i * DI1 * (N.qOut i * DO2) := by positivity
        have hdi2 : 0 ≤ DI2 := (hdi _).1
        have hdo1 : 0 ≤ DO1 := (hdo _).1
        have hprod : DO1 * DI2 ≤ DO2 * DI1 :=
          mul_le_mul mo1 mo2 hdi2 (le_trans hdo1 mo1)
        have key : a * c * (N.qIn i * DI1 * (N.qOut i * DO2)) =
            b ^ 2 * (N.qOut i * N.qIn i * (DO1 * DI2)) := by
          have h1 : a * N.qIn i * DI1 = b * N.qOut i * DO1 := fl1
          have h2 : b * N.qIn i * DI2 = c * N.qOut i * DO2 := fl2
          linear_combination (c * N.qOut i * DO2) * h1 - (b * N.qOut i * DO1) * h2
        have hle : a * c * (N.qIn i * DI1 * (N.qOut i * DO2)) ≤
            b ^ 2 * (N.qIn i * DI1 * (N.qOut i * DO2)) := by
          rw [key]
          have hq : 0 ≤ N.qOut i * N.qIn i := by positivity
          have := mul_le_mul_of_nonneg_left hprod hq
          have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
          nlinarith
        exact le_of_mul_le_mul_right hle hK
      · rw [← hc, mul_zero]; exact sq_nonneg _
    · rw [← ha, zero_mul]; exact sq_nonneg _
