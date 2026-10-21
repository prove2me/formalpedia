-- Prove2me | solution 1 for HiringLP.SimUpper.ec15_chain
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:11:39.799604+00:00
-- url     : https://prove2.me/submissions/88ae60bd-ff63-4d0e-a94a-ce1f3a9a1475

import Mathlib
import Definitions.Def_HiringLP_SimUpper_Model
import Definitions.Def_HiringLP_SimUpper_HardInstance
import Definitions.Def_HiringLP_SimUpper_Binomial

set_option autoImplicit false
open HiringLP.SimUpper Finset

theorem setProb_sub_HSU {n : ℕ} (S A : Finset (Fin n)) (q : ℝ) :
    setProb (fun i => (if i ∈ S then q else 0)) A =
      if A ⊆ S then q ^ A.card * (1 - q) ^ (S.card - A.card) else 0 := by
  unfold setProb
  split_ifs with h
  · have h1 : ∏ i : Fin n, (if i ∈ A then (if i ∈ S then q else 0) else 1 - (if i ∈ S then q else 0))
        = ∏ i ∈ S, (if i ∈ A then q else 1 - q) := by
      rw [← Finset.prod_subset (Finset.subset_univ S)]
      · apply prod_congr rfl
        intro i hi
        simp [hi]
      · intro i _ hi
        have : i ∉ A := fun hA => hi (h hA)
        simp [this, hi]
    rw [h1, Finset.prod_ite]
    have e1 : S.filter (fun i => i ∈ A) = A := by
      ext i; simp only [mem_filter]; exact ⟨fun h => h.2, fun hi => ⟨h hi, hi⟩⟩
    have e2 : S.filter (fun i => ¬ i ∈ A) = S \ A := by
      ext i; simp [mem_sdiff]
    rw [e1, e2, Finset.prod_const, Finset.prod_const, Finset.card_sdiff_of_subset h]
  · have : ∃ i, i ∈ A ∧ i ∉ S := by
      by_contra hc
      push_neg at hc
      exact h hc
    obtain ⟨i, hiA, hiS⟩ := this
    apply prod_eq_zero (Finset.mem_univ i)
    simp [hiA, hiS]

theorem core_HSU {n : ℕ} (I : SimInstance n) (S : Finset (Fin n)) (q w : ℝ)
    (hp : ∀ i ∈ S, I.p i = q) (hv : ∀ i ∈ S, I.v i = w) :
    reward I S = ∑ t ∈ range (S.card + 1), (S.card.choose t : ℝ) *
      (q ^ t * (1 - q) ^ (S.card - t) * (w * t - max ((t : ℝ) - I.k) 0)) := by
  unfold reward rewardIndep
  have hq : (fun i : Fin n => (if i ∈ S then (1 : ℝ) else 0) * I.p i) =
      fun i => if i ∈ S then q else 0 := by
    funext i
    by_cases hi : i ∈ S
    · simp [hi, hp i hi]
    · simp [hi]
  rw [hq]
  simp_rw [setProb_sub_HSU S]
  rw [← Finset.sum_subset (Finset.subset_univ S.powerset)]
  · have : ∀ A ∈ S.powerset,
        (if A ⊆ S then q ^ A.card * (1 - q) ^ (S.card - A.card) else 0) *
          ((∑ i ∈ A, I.v i) - max ((A.card : ℝ) - I.k) 0) =
        (fun t : ℕ => q ^ t * (1 - q) ^ (S.card - t) * (w * t - max ((t : ℝ) - I.k) 0)) A.card := by
      intro A hA
      have hAS : A ⊆ S := mem_powerset.1 hA
      rw [if_pos hAS]
      have : ∑ i ∈ A, I.v i = w * A.card := by
        rw [sum_congr rfl (fun i hi => hv i (hAS hi))]; simp [mul_comm]
      rw [this]
    rw [sum_congr rfl this, Finset.sum_powerset_apply_card (fun t : ℕ => q ^ t * (1 - q) ^ (S.card - t) * (w * t - max ((t : ℝ) - I.k) 0))]
    simp only [nsmul_eq_mul]
  · intro A _ hA
    have : ¬ A ⊆ S := fun h => hA (mem_powerset.2 h)
    rw [if_neg this]; simp

theorem binom_one_HSU (m : ℕ) (q : ℝ) : ∑ t ∈ range (m + 1), binomPMF m q t = 1 := by
  have := add_pow q (1 - q) m
  simp only [add_sub_cancel, one_pow] at this
  rw [this]
  apply sum_congr rfl
  intro t _
  unfold binomPMF; ring

theorem binom_mean_HSU (m : ℕ) (q : ℝ) : ∑ t ∈ range (m + 1), (t : ℝ) * binomPMF m q t = m * q := by
  rcases m with _ | m
  · simp [binomPMF]
  rw [sum_range_succ']
  have : ∀ t ∈ range (m + 1), (((t + 1 : ℕ) : ℝ)) * binomPMF (m + 1) q (t + 1) =
      ((m + 1 : ℕ) : ℝ) * q * binomPMF m q t := by
    intro t ht
    have ht' : t ≤ m := by have := mem_range.1 ht; omega
    have hc := Nat.add_one_mul_choose_eq m t
    have hc' : (((m + 1 : ℕ) : ℝ)) * (m.choose t : ℝ) = ((m + 1).choose (t + 1) : ℝ) * ((t : ℝ) + 1) := by
      exact_mod_cast hc
    unfold binomPMF
    have e : m + 1 - (t + 1) = m - t := by omega
    rw [e]
    push_cast
    have : ((m : ℝ) + 1) * (m.choose t : ℝ) = ((m + 1).choose (t + 1) : ℝ) * ((t : ℝ) + 1) := by
      push_cast at hc'; exact hc'
    calc ((t : ℝ) + 1) * (((m + 1).choose (t + 1) : ℝ) * q ^ (t + 1) * (1 - q) ^ (m - t))
        = (((m + 1).choose (t + 1) : ℝ) * ((t : ℝ) + 1)) * (q ^ (t + 1) * (1 - q) ^ (m - t)) := by ring
      _ = (((m : ℝ) + 1) * (m.choose t : ℝ)) * (q ^ (t + 1) * (1 - q) ^ (m - t)) := by rw [this]
      _ = ((m : ℝ) + 1) * q * ((m.choose t : ℝ) * q ^ t * (1 - q) ^ (m - t)) := by ring
  rw [sum_congr rfl this, ← mul_sum, binom_one_HSU]
  simp

theorem binom_nonneg_HSU (m : ℕ) (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (t : ℕ) : 0 ≤ binomPMF m q t := by
  unfold binomPMF
  have : 0 ≤ 1 - q := by linarith
  positivity

theorem reward_hard_HSU (k j m : ℕ) (ε τ : ℝ) (hk : 1 ≤ k) (hkj : k ≤ j) (hm : m ≤ j ^ 2) :
    reward (hardInstance k j ε τ) (valueOrdered m) =
      ∑ t ∈ range (m + 1), binomPMF m ((k : ℝ) / j) t *
        ((τ + ε * τ / j) * t - max ((t : ℝ) - k) 0) := by
  have hcard : (valueOrdered (n := j ^ 2 + k) m).card = m := by
    unfold valueOrdered
    rw [Fin.card_filter_val_lt]; omega
  have := core_HSU (hardInstance k j ε τ) (valueOrdered m) ((k : ℝ) / j) (τ + ε * τ / j)
    (by
      intro i hi
      have : i.val < m := by simpa [valueOrdered] using hi
      have : i.val < j ^ 2 := by omega
      simp [hardInstance, this])
    (by
      intro i hi
      have : i.val < m := by simpa [valueOrdered] using hi
      have : i.val < j ^ 2 := by omega
      simp [hardInstance, this])
  rw [this, hcard]
  apply sum_congr rfl
  intro t _
  unfold binomPMF
  simp only [hardInstance]
  ring

theorem exp_form_HSU (m k : ℕ) (q w : ℝ) :
    ∑ t ∈ range (m + 1), binomPMF m q t * (w * t - max ((t : ℝ) - k) 0) =
      w * (m * q) - m * q + expMinBinom m q k := by
  have h1 : ∑ t ∈ range (m + 1), binomPMF m q t * (w * t - max ((t : ℝ) - k) 0) =
      ∑ t ∈ range (m + 1), (w * ((t : ℝ) * binomPMF m q t) - (t : ℝ) * binomPMF m q t +
        min (t : ℝ) k * binomPMF m q t) := by
    apply sum_congr rfl
    intro t _
    have : max ((t : ℝ) - k) 0 = (t : ℝ) - min (t : ℝ) k := by
      rcases le_total (t : ℝ) k with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith)]
    rw [this]; ring
  rw [h1, sum_add_distrib, sum_sub_distrib, ← mul_sum, binom_mean_HSU]
  unfold expMinBinom
  ring

theorem solution (k j m : ℕ) (ε τ : ℝ) (hk : 1 ≤ k) (hkj : k ≤ j) (hε : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hm : m ≤ j ^ 2) :
    reward (hardInstance k j ε τ) (valueOrdered m) =
        (τ + ε * τ / j) * k * m / j +
          ∑ t ∈ range (m + 1), binomPMF m ((k : ℝ) / j) t * min 0 ((k : ℝ) - t) ∧
    reward (hardInstance k j ε τ) (valueOrdered m) ≤
        k + k * m / j * (τ + ε * τ / j - tailBinom m ((k : ℝ) / j) k) := by
  have hj : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hq0 : 0 ≤ (k : ℝ) / j := by positivity
  have hq1 : (k : ℝ) / j ≤ 1 := by
    rw [div_le_one hj]; exact_mod_cast hkj
  set q : ℝ := (k : ℝ) / j with hq
  set w : ℝ := τ + ε * τ / j with hw
  have hR := reward_hard_HSU k j m ε τ hk hkj hm
  have hT : ∑ t ∈ range (m + 1), binomPMF m q t * ((τ + ε * τ / j) * t - max ((t : ℝ) - k) 0) =
      w * (m * q) + ∑ t ∈ range (m + 1), binomPMF m q t * min 0 ((k : ℝ) - t) := by
    have : ∀ t ∈ range (m + 1), binomPMF m q t * ((τ + ε * τ / j) * t - max ((t : ℝ) - k) 0) =
        w * ((t : ℝ) * binomPMF m q t) + binomPMF m q t * min 0 ((k : ℝ) - t) := by
      intro t _
      have : max ((t : ℝ) - k) 0 = - min 0 ((k : ℝ) - t) := by
        rcases le_total (t : ℝ) k with h | h
        · rw [min_eq_left (by linarith), max_eq_right (by linarith)]; ring
        · rw [min_eq_right (by linarith), max_eq_left (by linarith)]; ring
      rw [this]; ring
    rw [sum_congr rfl this, sum_add_distrib, ← mul_sum, binom_mean_HSU]
  have hid : reward (hardInstance k j ε τ) (valueOrdered m) =
      (τ + ε * τ / j) * k * m / j +
          ∑ t ∈ range (m + 1), binomPMF m q t * min 0 ((k : ℝ) - t) := by
    rw [hR, hT, hq]; ring
  refine ⟨hid, ?_⟩
  rw [hid]
  have hS : ∑ t ∈ range (m + 1), binomPMF m q t * min 0 ((k : ℝ) - t) ≤ k - m * q := by
    have h1 : ∑ t ∈ range (m + 1), binomPMF m q t * min 0 ((k : ℝ) - t) ≤
        ∑ t ∈ range (m + 1), (k * binomPMF m q t - (t : ℝ) * binomPMF m q t) := by
      apply sum_le_sum
      intro t _
      have := binom_nonneg_HSU m q hq0 hq1 t
      have h2 : min 0 ((k : ℝ) - t) ≤ (k : ℝ) - t := min_le_right _ _
      nlinarith
    rw [sum_sub_distrib, ← mul_sum, binom_one_HSU, binom_mean_HSU] at h1
    linarith
  have hTail : tailBinom m q k ≤ 1 := by
    unfold tailBinom
    calc ∑ t ∈ range (m + 1), (if k < t then binomPMF m q t else 0)
        ≤ ∑ t ∈ range (m + 1), binomPMF m q t := by
          apply sum_le_sum
          intro t _
          split_ifs
          · exact le_rfl
          · exact binom_nonneg_HSU m q hq0 hq1 t
      _ = 1 := binom_one_HSU m q
  have hmq : (0 : ℝ) ≤ m * q := by positivity
  have e : (τ + ε * τ / j) * k * m / j = w * (m * q) := by rw [hw, hq]; ring
  have e2 : (k : ℝ) * m / j = m * q := by rw [hq]; ring
  rw [e, e2]
  nlinarith
