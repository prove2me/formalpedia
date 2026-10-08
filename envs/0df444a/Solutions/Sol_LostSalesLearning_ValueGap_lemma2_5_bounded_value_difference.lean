-- Prove2me | solution 1 for LostSalesLearning.ValueGap.lemma2_5_bounded_value_difference
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T23:57:26.329504+00:00
-- url     : https://prove2.me/submissions/ff7edaf3-7651-403d-8d7f-db344dfd71b0

import Mathlib
import Definitions.Def_LostSalesLearning_ValueGap_Setting

open MeasureTheory
open scoped NNReal

namespace LSL85fcdf92

open LostSalesLearning.ValueGap

/-- Cumulative-sales potential: for `k < L` the (negated) pipeline tail, afterwards total sales. -/
noncomputable def Mf {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (k : ℕ) : ℝ :=
  if k < L then -(∑ i : Fin (L + 1), if k < (i : ℕ) then s i else 0)
  else totalSales s d (k - L)

lemma Mf_ge {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t : ℕ) :
    Mf s d (L + t) = totalSales s d t := by
  unfold Mf
  rw [if_neg (by omega)]
  congr 1; omega

lemma step_zero {n : ℕ} (s : Fin (n + 2) → ℝ) (dt : ℝ) :
    step s dt 0 = s 0 - min (s 0) dt + s 1 := by
  unfold step
  rw [Function.update_self]
  congr 1

lemma step_mid {n : ℕ} (s : Fin (n + 2) → ℝ) (dt : ℝ) (j : Fin (n + 2)) (hj : 0 < (j : ℕ))
    (hjL : (j : ℕ) < n + 1) : step s dt j = s ⟨(j : ℕ) + 1, by omega⟩ := by
  unfold step
  rw [Function.update_of_ne (by intro h; subst h; simp at hj)]
  obtain ⟨i, rfl⟩ : ∃ i : Fin (n + 1), j = Fin.castSucc i := ⟨⟨j, hjL⟩, Fin.ext rfl⟩
  rw [Fin.snoc_castSucc]
  rfl

lemma step_last {n : ℕ} (s : Fin (n + 2) → ℝ) (dt : ℝ) :
    step s dt (Fin.last (n + 1)) = min (s 0) dt := by
  unfold step
  rw [Function.update_of_ne (by intro h; exact absurd (congrArg Fin.val h) (by simp)),
    Fin.snoc_last]

lemma Mf_succ_lt {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (k : ℕ) (hk : k + 1 ≤ L) :
    Mf s d (k + 1) - Mf s d k = s ⟨k + 1, by omega⟩ := by
  have hpre : Mf s d k = -(∑ i : Fin (L + 1), if k < (i : ℕ) then s i else 0) := by
    unfold Mf; rw [if_pos (by omega)]
  have hpost : Mf s d (k + 1) = -(∑ i : Fin (L + 1), if k + 1 < (i : ℕ) then s i else 0) := by
    unfold Mf
    by_cases h : k + 1 < L
    · rw [if_pos h]
    · rw [if_neg h]
      have hk' : k + 1 = L := by omega
      have : k + 1 - L = 0 := by omega
      rw [this]
      simp only [totalSales, Finset.range_zero, Finset.sum_empty]
      symm
      rw [neg_eq_zero]
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      have := i.isLt
      omega
  rw [hpre, hpost]
  have : ∀ i : Fin (L + 1), ((if k < (i : ℕ) then s i else 0) - (if k + 1 < (i : ℕ) then s i else 0))
      = if i = (⟨k + 1, by omega⟩ : Fin (L + 1)) then s i else 0 := by
    intro i
    by_cases h1 : (i : ℕ) = k + 1
    · have : i = (⟨k + 1, by omega⟩ : Fin (L + 1)) := Fin.ext h1
      rw [if_pos (by omega), if_neg (by omega), if_pos this]; ring
    · have hne : i ≠ (⟨k + 1, by omega⟩ : Fin (L + 1)) := fun h => h1 (by rw [h])
      rw [if_neg hne]
      by_cases h2 : k < (i : ℕ)
      · rw [if_pos h2, if_pos (by omega)]; ring
      · rw [if_neg h2, if_neg (by omega)]; ring
  have h3 := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => this i)
  rw [Finset.sum_sub_distrib] at h3
  rw [Finset.sum_ite_eq' Finset.univ] at h3
  simp only [Finset.mem_univ, if_true] at h3
  linarith

lemma Mf_succ_ge {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t : ℕ) :
    Mf s d (L + t + 1) - Mf s d (L + t) = sales s d t := by
  rw [show L + t + 1 = L + (t + 1) by omega, Mf_ge, Mf_ge]
  simp only [totalSales, Finset.sum_range_succ]
  ring

/-- Structural invariant of the trajectory. -/
lemma traj_inv {n : ℕ} (x : ℝ) (s : Fin (n + 2) → ℝ) (hsum : ∑ i, s i = x)
    (d : ℕ → ℝ≥0) (t : ℕ) :
    traj s d t 0 = x + Mf s d t - Mf s d (n + 1 + t) ∧
    ∀ j : Fin (n + 2), 0 < (j : ℕ) →
      traj s d t j = Mf s d (t + j) - Mf s d (t + j - 1) := by
  induction t with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [traj_zero, add_zero]
      have hL : Mf s d (n + 1) = 0 := by
        have := Mf_ge s d 0
        simpa [totalSales] using this
      rw [hL]
      have h0 : Mf s d 0 = -(∑ i : Fin (n + 2), if 0 < (i : ℕ) then s i else 0) := by
        unfold Mf; rw [if_pos (by omega)]
      rw [h0, ← hsum, Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun i : Fin (n + 2) =>
        if 0 < (i : ℕ) then s i else 0)]
      simp
    · intro j hj
      simp only [traj_zero, zero_add]
      obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = k + 1 := ⟨(j : ℕ) - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, Mf_succ_lt s d k (by have := j.isLt; omega)]
      congr 1; exact Fin.ext hk
  | succ t ih =>
    obtain ⟨ih0, ihj⟩ := ih
    have h1 := ihj 1 (by simp)
    simp only [Fin.val_one] at h1
    refine ⟨?_, ?_⟩
    · rw [traj_succ, step_zero, ih0, h1]
      have hs : sales s d t = min (traj s d t 0) (d t) := rfl
      rw [ih0] at hs
      have := Mf_succ_ge s d t
      rw [show n + 1 + (t + 1) = n + 1 + t + 1 by omega, ← hs]
      simp only [Nat.add_sub_cancel] at *
      linarith
    · intro j hj
      rw [traj_succ]
      by_cases hjL : (j : ℕ) < n + 1
      · rw [step_mid _ _ j hj hjL, ihj _ (by simp)]
        simp only
        congr 2 <;> omega
      · have hjl : j = Fin.last (n + 1) := Fin.ext (by have := j.isLt; simp; omega)
        rw [hjl, step_last]
        have hs : sales s d t = min (traj s d t 0) (d t) := rfl
        rw [← hs, ← Mf_succ_ge s d t]
        simp only [Fin.val_last]
        congr 2 <;> omega

lemma traj_nonneg {n : ℕ} (s : Fin (n + 2) → ℝ) (hs : ∀ i, 0 ≤ s i) (d : ℕ → ℝ≥0) :
    ∀ t j, 0 ≤ traj s d t j := by
  intro t
  induction t with
  | zero => intro j; simpa using hs j
  | succ t ih =>
    intro j
    rw [traj_succ]
    by_cases h0 : j = 0
    · subst h0
      rw [step_zero]
      have := min_le_left (traj s d t 0) (d t)
      have := ih 1
      linarith
    · have hj : 0 < (j : ℕ) := by
        rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
        · exact absurd (Fin.ext h) h0
        · exact h
      by_cases hjL : (j : ℕ) < n + 1
      · rw [step_mid _ _ j hj hjL]; exact ih _
      · have hjl : j = Fin.last (n + 1) := Fin.ext (by have := j.isLt; simp; omega)
        rw [hjl, step_last]
        exact le_min (ih 0) (d t).2

lemma sales_nonneg {n : ℕ} (s : Fin (n + 2) → ℝ) (hs : ∀ i, 0 ≤ s i) (d : ℕ → ℝ≥0) (t : ℕ) :
    0 ≤ sales s d t := le_min (traj_nonneg s hs d t 0) (d t).2

lemma Mf_mono {n : ℕ} (s : Fin (n + 2) → ℝ) (hs : ∀ i, 0 ≤ s i) (d : ℕ → ℝ≥0) :
    Monotone (Mf s d) := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hk : k + 1 ≤ n + 1
  · have := Mf_succ_lt s d k hk
    have := hs ⟨k + 1, by omega⟩
    linarith
  · obtain ⟨t, rfl⟩ : ∃ t, k = n + 1 + t := ⟨k - (n + 1), by omega⟩
    have := Mf_succ_ge s d t
    have := sales_nonneg s hs d t
    linarith

lemma Mf_pre {L : ℕ} (x : ℝ) (s : Fin (L + 1) → ℝ) (hs : s ∈ Sx L x) (d : ℕ → ℝ≥0) (k : ℕ)
    (hk : k < L) : -x ≤ Mf s d k ∧ Mf s d k ≤ 0 := by
  have h : Mf s d k = -(∑ i : Fin (L + 1), if k < (i : ℕ) then s i else 0) := by
    unfold Mf; rw [if_pos hk]
  rw [h]
  have h1 : 0 ≤ ∑ i : Fin (L + 1), (if k < (i : ℕ) then s i else 0) :=
    Finset.sum_nonneg fun i _ => by split_ifs <;> [exact hs.1 i; exact le_rfl]
  have h2 : ∑ i : Fin (L + 1), (if k < (i : ℕ) then s i else 0) ≤ ∑ i, s i :=
    Finset.sum_le_sum fun i _ => by split_ifs <;> [exact le_rfl; exact hs.1 i]
  rw [hs.2] at h2
  constructor <;> linarith

lemma Mf_rec {n : ℕ} (x : ℝ) (s : Fin (n + 2) → ℝ) (hsum : ∑ i, s i = x) (d : ℕ → ℝ≥0)
    (t : ℕ) : Mf s d (n + 1 + t + 1) = min (x + Mf s d t) (Mf s d (n + 1 + t) + d t) := by
  have h1 := Mf_succ_ge s d t
  have h2 : sales s d t = min (traj s d t 0) (d t) := rfl
  rw [(traj_inv x s hsum d t).1] at h2
  rw [h2] at h1
  rw [show Mf s d (n + 1 + t + 1) = Mf s d (n + 1 + t) +
      min (x + Mf s d t - Mf s d (n + 1 + t)) (d t) by linarith]
  rw [← min_add_add_left]
  congr 1 <;> ring

lemma Mf_close {n : ℕ} (x : ℝ) (s s' : Fin (n + 2) → ℝ) (hs : s ∈ Sx (n + 1) x)
    (hs' : s' ∈ Sx (n + 1) x) (d : ℕ → ℝ≥0) : ∀ k, |Mf s d k - Mf s' d k| ≤ x := by
  have hx : 0 ≤ x := by rw [← hs.2]; exact Finset.sum_nonneg fun i _ => hs.1 i
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < n + 1
    · have a := Mf_pre x s hs d k hk
      have b := Mf_pre x s' hs' d k hk
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨t, rfl⟩ : ∃ t, k = n + 1 + t := ⟨k - (n + 1), by omega⟩
      cases t with
      | zero =>
        rw [Mf_ge, Mf_ge]; simpa [totalSales] using hx
      | succ t =>
        rw [← add_assoc, Mf_rec x s hs.2, Mf_rec x s' hs'.2]
        refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
        · have := ih t (by omega)
          rw [show x + Mf s d t - (x + Mf s' d t) = Mf s d t - Mf s' d t by ring]
          exact this
        · have := ih (n + 1 + t) (by omega)
          rw [show Mf s d (n + 1 + t) + (d t : ℝ) - (Mf s' d (n + 1 + t) + d t)
            = Mf s d (n + 1 + t) - Mf s' d (n + 1 + t) by ring]
          exact this

lemma costSum_eq {n : ℕ} (h p x : ℝ) (s : Fin (n + 2) → ℝ) (hsum : ∑ i, s i = x)
    (d : ℕ → ℝ≥0) (T : ℕ) :
    ∑ t ∈ Finset.range T, pseudoCost h p s d t =
      h * ∑ t ∈ Finset.range T, (x + Mf s d t - Mf s d (n + 1 + t)) - (h + p) * Mf s d (n + 1 + T) := by
  rw [Mf_ge]
  unfold totalSales
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  unfold pseudoCost onHand
  rw [(traj_inv x s hsum d t).1]
  ring

lemma tele (f : ℕ → ℝ) (T L : ℕ) :
    ∑ t ∈ Finset.range T, (f t - f (L + t)) =
      ∑ t ∈ Finset.range L, f t - ∑ t ∈ Finset.range L, f (T + t) := by
  have h1 := Finset.sum_range_add f T L
  have h2 := Finset.sum_range_add f L T
  rw [add_comm T L] at h1
  rw [Finset.sum_sub_distrib]
  linarith

lemma sum_abs_bound (f : ℕ → ℝ) (x : ℝ) (hf : ∀ k, |f k| ≤ x) (L : ℕ) :
    |∑ t ∈ Finset.range L, f t| ≤ L * x := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun t _ => hf t).trans ?_
  simp

lemma path_bound {n : ℕ} (h p x : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (s s' : Fin (n + 2) → ℝ)
    (hs : s ∈ Sx (n + 1) x) (hs' : s' ∈ Sx (n + 1) x) (d : ℕ → ℝ≥0) (T : ℕ) :
    ∑ t ∈ Finset.range T, pseudoCost h p s d t - ∑ t ∈ Finset.range T, pseudoCost h p s' d t
      ≤ h * (2 * ((n + 1 : ℕ) : ℝ) * x) + (h + p) * x := by
  rw [costSum_eq h p x s hs.2, costSum_eq h p x s' hs'.2]
  set D : ℕ → ℝ := fun k => Mf s d k - Mf s' d k with hD
  have hDb : ∀ k, |D k| ≤ x := Mf_close x s s' hs hs' d
  have key : ∑ t ∈ Finset.range T, (x + Mf s d t - Mf s d (n + 1 + t)) -
      ∑ t ∈ Finset.range T, (x + Mf s' d t - Mf s' d (n + 1 + t)) =
      ∑ t ∈ Finset.range T, (D t - D (n + 1 + t)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    simp only [hD]; ring
  rw [tele D T (n + 1)] at key
  have b1 := sum_abs_bound D x hDb (n + 1)
  have b2 := sum_abs_bound (fun t => D (T + t)) x (fun k => hDb _) (n + 1)
  have hS : ∑ t ∈ Finset.range T, (x + Mf s d t - Mf s d (n + 1 + t)) -
      ∑ t ∈ Finset.range T, (x + Mf s' d t - Mf s' d (n + 1 + t)) ≤ 2 * ((n + 1 : ℕ) : ℝ) * x := by
    rw [key]
    have := (abs_le.mp b1).2
    have := (abs_le.mp b2).1
    linarith
  have hlast := (abs_le.mp (hDb (n + 1 + T))).1
  have e1 := mul_le_mul_of_nonneg_left hS hh
  have e2 := mul_le_mul_of_nonneg_left (show -(Mf s d (n + 1 + T) - Mf s' d (n + 1 + T)) ≤ x by
    simp only [hD] at hlast; linarith) (add_nonneg hh hp)
  nlinarith [e1, e2]

lemma Mf_meas {n : ℕ} (x : ℝ) (s : Fin (n + 2) → ℝ) (hsum : ∑ i, s i = x) :
    ∀ k, Measurable (fun d : ℕ → ℝ≥0 => Mf s d k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < n + 1
    · have : (fun d : ℕ → ℝ≥0 => Mf s d k) =
          fun _ => -(∑ i : Fin (n + 2), if k < (i : ℕ) then s i else 0) := by
        funext d; unfold Mf; rw [if_pos hk]
      rw [this]; exact measurable_const
    · obtain ⟨t, rfl⟩ : ∃ t, k = n + 1 + t := ⟨k - (n + 1), by omega⟩
      cases t with
      | zero =>
        have : (fun d : ℕ → ℝ≥0 => Mf s d (n + 1 + 0)) = fun _ => 0 := by
          funext d; rw [Mf_ge]; simp [totalSales]
        rw [this]; exact measurable_const
      | succ t =>
        have : (fun d : ℕ → ℝ≥0 => Mf s d (n + 1 + (t + 1))) =
            fun d => min (x + Mf s d t) (Mf s d (n + 1 + t) + d t) := by
          funext d; rw [← add_assoc, Mf_rec x s hsum]
        rw [this]
        have hdt : Measurable (fun d : ℕ → ℝ≥0 => ((d t : ℝ≥0) : ℝ)) :=
          (measurable_pi_apply t).coe_nnreal_real
        exact ((ih t (by omega)).const_add x).min ((ih (n + 1 + t) (by omega)).add hdt)

lemma costSum_meas {n : ℕ} (h p x : ℝ) (s : Fin (n + 2) → ℝ) (hsum : ∑ i, s i = x) (T : ℕ) :
    Measurable (fun d : ℕ → ℝ≥0 => ∑ t ∈ Finset.range T, pseudoCost h p s d t) := by
  have : (fun d : ℕ → ℝ≥0 => ∑ t ∈ Finset.range T, pseudoCost h p s d t) =
      fun d => ∑ t ∈ Finset.range T,
        (h * ((x + Mf s d t - Mf s d (n + 1 + t)) - min (x + Mf s d t - Mf s d (n + 1 + t)) (d t))
          - p * min (x + Mf s d t - Mf s d (n + 1 + t)) (d t)) := by
    funext d
    apply Finset.sum_congr rfl
    intro t _
    unfold pseudoCost sales onHand
    rw [(traj_inv x s hsum d t).1]
  rw [this]
  refine Finset.measurable_sum _ fun t _ => ?_
  have hI : Measurable (fun d : ℕ → ℝ≥0 => x + Mf s d t - Mf s d (n + 1 + t)) :=
    ((Mf_meas x s hsum t).const_add x).sub (Mf_meas x s hsum (n + 1 + t))
  have hdt : Measurable (fun d : ℕ → ℝ≥0 => ((d t : ℝ≥0) : ℝ)) :=
    (measurable_pi_apply t).coe_nnreal_real
  exact ((hI.sub (hI.min hdt)).const_mul h).sub ((hI.min hdt).const_mul p)

lemma pseudoCost_abs {n : ℕ} (h p x : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (s : Fin (n + 2) → ℝ)
    (hs : s ∈ Sx (n + 1) x) (d : ℕ → ℝ≥0) (t : ℕ) :
    |pseudoCost h p s d t| ≤ (h + p) * x := by
  have hI0 : 0 ≤ onHand s d t := traj_nonneg s hs.1 d t 0
  have hIx : onHand s d t ≤ x := by
    unfold onHand
    rw [(traj_inv x s hs.2 d t).1]
    have := Mf_mono s hs.1 d (show t ≤ n + 1 + t by omega)
    linarith
  have hy0 : 0 ≤ sales s d t := sales_nonneg s hs.1 d t
  have hyI : sales s d t ≤ onHand s d t := min_le_left _ _
  unfold pseudoCost
  have e1 := mul_nonneg hh (sub_nonneg.2 hyI)
  have e2 := mul_le_mul_of_nonneg_left (show onHand s d t - sales s d t ≤ x by linarith) hh
  have e3 := mul_nonneg hp hy0
  have e4 := mul_le_mul_of_nonneg_left (show sales s d t ≤ x by linarith) hp
  rw [abs_le]; constructor <;> nlinarith

lemma costSum_integrable {n : ℕ} (h p x : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (F : Measure ℝ≥0) [IsProbabilityMeasure F] (s : Fin (n + 2) → ℝ) (hs : s ∈ Sx (n + 1) x)
    (T : ℕ) :
    Integrable (fun d : ℕ → ℝ≥0 => ∑ t ∈ Finset.range T, pseudoCost h p s d t)
      (Measure.infinitePi fun _ : ℕ => F) := by
  refine Integrable.of_bound (costSum_meas h p x s hs.2 T).aestronglyMeasurable
    (T * ((h + p) * x)) (Filter.Eventually.of_forall fun d => ?_)
  rw [Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun t _ => pseudoCost_abs h p x hh hp s hs d t).trans ?_
  simp

end LSL85fcdf92

open MeasureTheory NNReal LostSalesLearning.ValueGap in
theorem solution {L : ℕ} (h p x : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (F : Measure ℝ≥0) [IsProbabilityMeasure F] (T : ℕ) (s s' : Fin (L + 1) → ℝ)
    (hs : s ∈ Sx L x) (hs' : s' ∈ Sx L x) :
    value h p F T s - value h p F T s' ≤ 36 * max h p * (L : ℝ) * x := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · have hss : s = s' := by
      funext i
      obtain ⟨i, hi⟩ := i
      obtain rfl : i = 0 := by omega
      have h1 := hs.2
      have h2 := hs'.2
      rw [Fin.sum_univ_succ] at h1 h2
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at h1 h2
      exact h1.trans h2.symm
    subst hss
    simp
  · obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
    have hx : 0 ≤ x := by
      rw [← hs.2]; exact Finset.sum_nonneg fun i _ => hs.1 i
    have hB : value h p F T s - value h p F T s' ≤
        h * (2 * ((n + 1 : ℕ) : ℝ) * x) + (h + p) * x := by
      unfold value
      rw [← integral_sub (LSL85fcdf92.costSum_integrable h p x hh hp F s hs T)
        (LSL85fcdf92.costSum_integrable h p x hh hp F s' hs' T)]
      refine le_trans (integral_mono ((LSL85fcdf92.costSum_integrable h p x hh hp F s hs T).sub
        (LSL85fcdf92.costSum_integrable h p x hh hp F s' hs' T)) (integrable_const _)
        (fun d => LSL85fcdf92.path_bound h p x hh hp s s' hs hs' d T)) ?_
      simp
    have hm1 : h ≤ max h p := le_max_left h p
    have hm2 : p ≤ max h p := le_max_right h p
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hLx : 0 ≤ ((n + 1 : ℕ) : ℝ) * x := mul_nonneg (by positivity) hx
    have a1 : h * (2 * ((n + 1 : ℕ) : ℝ) * x) ≤ max h p * (2 * ((n + 1 : ℕ) : ℝ) * x) :=
      mul_le_mul_of_nonneg_right hm1 (by positivity)
    have a2 : (h + p) * x ≤ (2 * max h p) * (((n + 1 : ℕ) : ℝ) * x) := by
      have : x ≤ ((n + 1 : ℕ) : ℝ) * x := by nlinarith
      have hmax0 : 0 ≤ max h p := le_trans hh hm1
      calc (h + p) * x ≤ (2 * max h p) * x := mul_le_mul_of_nonneg_right (by linarith) hx
        _ ≤ (2 * max h p) * (((n + 1 : ℕ) : ℝ) * x) := mul_le_mul_of_nonneg_left this (by linarith)
    have a3 : 0 ≤ max h p * (((n + 1 : ℕ) : ℝ) * x) := mul_nonneg (le_trans hh hm1) hLx
    calc value h p F T s - value h p F T s' ≤ h * (2 * ((n + 1 : ℕ) : ℝ) * x) + (h + p) * x := hB
      _ ≤ 36 * max h p * ((n + 1 : ℕ) : ℝ) * x := by nlinarith
