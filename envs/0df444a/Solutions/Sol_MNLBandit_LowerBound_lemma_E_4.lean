-- Prove2me | solution 1 for MNLBandit.LowerBound.lemma_E_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:43:05.656935+00:00
-- url     : https://prove2.me/submissions/c86f7b75-eedc-48cf-93cc-7c44273ce1c1

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_MNLBandit_LowerBound_Setting

set_option autoImplicit false
open MNLBandit.LowerBound

lemma key_E4 (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) (hε : 0 ≤ ε) (S : Finset (Fin N)) :
    FoundationsRL.GeneralDM.klDivDiscrete
        (choiceProb 1 (instHat N ε false).v S) (choiceProb 1 (instHat N ε true).v S) ≤
      ENNReal.ofReal (4 * ε ^ 2) := by
  set i0 : Fin N := ⟨0, by omega⟩ with hi0
  have hv0 : ∀ i, (instHat N ε false).v i = 1 / 2 := by
    intro i; simp [instHat]
  have hv1 : ∀ i, (instHat N ε true).v i = 1 / 2 + if i = i0 then ε else 0 := by
    intro i
    simp only [instHat, hi0, Fin.ext_iff]
    split_ifs <;> simp_all
  by_cases h0 : i0 ∈ S
  · -- the interesting case
    set k : ℝ := (S.card : ℝ) with hk
    have hcard1 : 1 ≤ S.card := Finset.card_pos.2 ⟨i0, h0⟩
    have hk1 : 1 ≤ k := by
      rw [hk]; exact_mod_cast hcard1
    have hs0 : ∑ j ∈ S, (instHat N ε false).v j = k / 2 := by
      simp only [hv0, Finset.sum_const, nsmul_eq_mul]; rw [hk]; ring
    have hs1 : ∑ j ∈ S, (instHat N ε true).v j = k / 2 + ε := by
      simp only [hv1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.sum_ite_eq', if_pos h0]
      rw [hk]; ring
    set P := choiceProb 1 (instHat N ε false).v S with hP
    set Q := choiceProb 1 (instHat N ε true).v S with hQ
    have hD0 : 0 < 1 + k / 2 := by linarith
    have hD1 : 0 < 1 + (k / 2 + ε) := by linarith
    have hPn : P none = 1 / (1 + k / 2) := by simp [hP, choiceProb, hs0]
    have hQn : Q none = 1 / (1 + (k / 2 + ε)) := by simp [hQ, choiceProb, hs1]
    have hPs : ∀ i, P (some i) = if i ∈ S then (1 / 2) / (1 + k / 2) else 0 := by
      intro i; simp only [hP, choiceProb]; rw [hs0, hv0]
    have hQs : ∀ i, Q (some i) =
        if i ∈ S then (1 / 2 + if i = i0 then ε else 0) / (1 + (k / 2 + ε)) else 0 := by
      intro i; simp only [hQ, choiceProb]; rw [hs1, hv1]
    have hQpos : ∀ y, P y ≠ 0 → 0 < Q y := by
      intro y hy
      cases y with
      | none => rw [hQn]; positivity
      | some i =>
        rw [hPs] at hy
        by_cases hi : i ∈ S
        · rw [hQs, if_pos hi]
          have : 0 ≤ (if i = i0 then ε else 0) := by split_ifs <;> linarith
          apply div_pos <;> linarith
        · simp [hi] at hy
    have hP0 : ∀ y, 0 ≤ P y := by
      intro y
      cases y with
      | none => rw [hPn]; positivity
      | some i => rw [hPs]; split_ifs <;> positivity
    unfold FoundationsRL.GeneralDM.klDivDiscrete
    rw [if_pos (by
      intro y hy
      by_contra hne
      exact absurd hy (hQpos y hne).ne')]
    apply ENNReal.ofReal_le_ofReal
    have hterm : ∀ y, P y * Real.log (P y / Q y) ≤ P y * (P y / Q y - 1) := by
      intro y
      by_cases hy : P y = 0
      · simp [hy]
      · exact mul_le_mul_of_nonneg_left
          (Real.log_le_sub_one_of_pos (div_pos (lt_of_le_of_ne (hP0 y) (Ne.symm hy)) (hQpos y hy)))
          (hP0 y)
    refine (Finset.sum_le_sum (fun y _ => hterm y)).trans ?_
    rw [Fintype.sum_option]
    have hsome : ∀ f : Fin N → ℝ, ∑ i, (if i ∈ S then f i else 0) = ∑ i ∈ S, f i := by
      intro f; simp [Finset.sum_ite_mem]
    have hrest : ∑ i : Fin N, P (some i) * (P (some i) / Q (some i) - 1) =
        ∑ i ∈ S, ((1 / 2) / (1 + k / 2) *
          (((1 / 2) / (1 + k / 2)) /
            ((1 / 2 + if i = i0 then ε else 0) / (1 + (k / 2 + ε))) - 1)) := by
      rw [← hsome]
      apply Finset.sum_congr rfl
      intro i _
      rw [hPs, hQs]
      split_ifs <;> simp
    rw [hrest, ← Finset.add_sum_erase S _ h0, hPn, hQn]
    rw [Finset.sum_congr rfl (g := fun _ => ((1 / 2) / (1 + k / 2) *
          (((1 / 2) / (1 + k / 2)) / ((1 / 2) / (1 + (k / 2 + ε))) - 1)))
      (by
        intro i hi
        have : i ≠ i0 := (Finset.mem_erase.1 hi).1
        simp [this])]
    rw [Finset.sum_const, Finset.card_erase_of_mem h0, nsmul_eq_mul]
    have hc : ((S.card - 1 : ℕ) : ℝ) = k - 1 := by
      rw [Nat.cast_sub hcard1]; simp [hk]
    rw [hc]
    simp only [if_true]
    have hk2 : 0 < k + 2 := by linarith
    have e : 1 / (1 + k / 2) * (1 / (1 + k / 2) / (1 / (1 + (k / 2 + ε))) - 1) +
        (1 / 2 / (1 + k / 2) * (1 / 2 / (1 + k / 2) / ((1 / 2 + ε) / (1 + (k / 2 + ε))) - 1) +
        (k - 1) * (1 / 2 / (1 + k / 2) * (1 / 2 / (1 + k / 2) / (1 / 2 / (1 + (k / 2 + ε))) - 1)))
        = 4 * ε ^ 2 * (k + 1) / ((1 + 2 * ε) * (k + 2) ^ 2) := by
      have : (1 + 2 * ε) ≠ 0 := by positivity
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ε, mul_nonneg (sq_nonneg ε) hε, mul_nonneg (sq_nonneg ε) (by linarith : (0:ℝ) ≤ k),
      mul_nonneg (mul_nonneg (sq_nonneg ε) hε) (by linarith : (0:ℝ) ≤ k),
      mul_nonneg (sq_nonneg ε) (mul_nonneg (by linarith : (0:ℝ) ≤ k) (by linarith : (0:ℝ) ≤ k))]
  · -- i0 ∉ S : the two laws coincide
    have hsum : ∑ j ∈ S, (instHat N ε true).v j = ∑ j ∈ S, (instHat N ε false).v j := by
      apply Finset.sum_congr rfl
      intro j hj
      have : j ≠ i0 := fun h => h0 (h ▸ hj)
      rw [hv1, hv0]; simp [this]
    have hPQ : choiceProb 1 (instHat N ε true).v S = choiceProb 1 (instHat N ε false).v S := by
      funext y
      cases y with
      | none => simp [choiceProb, hsum]
      | some i =>
        simp only [choiceProb]
        split_ifs with hi
        · have : i ≠ i0 := fun h => h0 (h ▸ hi)
          rw [hv1, hv0, hsum]; simp [this]
        · rfl
    rw [hPQ]
    unfold FoundationsRL.GeneralDM.klDivDiscrete
    rw [if_pos (fun _ h => h)]
    have : ∀ y, choiceProb 1 (instHat N ε false).v S y *
        Real.log (choiceProb 1 (instHat N ε false).v S y / choiceProb 1 (instHat N ε false).v S y) = 0 := by
      intro y
      by_cases hy : choiceProb 1 (instHat N ε false).v S y = 0
      · simp [hy]
      · simp [div_self hy]
    simp [this]

theorem solution (N T : ℕ) (hN : 2 ≤ N) (hT : 1 ≤ T) (S : Finset (Fin N)) :
    FoundationsRL.GeneralDM.klDivDiscrete
        (choiceProb (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) false).v₀
          (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) false).v S)
        (choiceProb (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) true).v₀
          (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) true).v S) ≤
      ENNReal.ofReal (4 * (Real.sqrt (1 / (32 * (T : ℝ)))) ^ 2) :=
  key_E4 N hN _ (Real.sqrt_nonneg _) S
