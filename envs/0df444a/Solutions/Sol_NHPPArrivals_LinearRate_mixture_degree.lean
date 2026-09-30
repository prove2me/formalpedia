-- Prove2me | solution 1 for NHPPArrivals.LinearRate.mixture_degree
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:37:12.159286+00:00
-- url     : https://prove2.me/submissions/9cd20c6b-2c61-45ec-911d-bc246cec21b9

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf
import Theorems.Thm_NHPPArrivals_LinearRate_linear_pieces_pos
import Theorems.Thm_NHPPArrivals_LinearRate_linear_pieces_zero

open MeasureTheory
open NHPPArrivals.LinearRate

theorem solution (a b T : ℝ) (k : ℕ) (hT : 0 < T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a ∨ 0 < b) (hk : 1 ≤ k) :
    IsGreatest ((fun t => |mixCdf (linRate a b) T k t - t|) '' Set.Icc (0:ℝ) 1)
      (degree (mixCdf (linRate a b) T k)) ∧
    (∀ j ∈ Finset.Icc 1 k,
      IsGreatest ((fun t => |subCdf (linRate a b) T k j t - t|) '' Set.Icc (0:ℝ) 1)
        (degree (subCdf (linRate a b) T k j))) ∧
    degree (mixCdf (linRate a b) T k) =
      ∑ j ∈ Finset.Icc 1 k,
        weight (linRate a b) T k j * degree (subCdf (linRate a b) T k j) := by
  have hkpos : 0 < k := by omega
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hkpos)
  have hcard : ((Finset.Icc 1 k).card : ℝ) = k := by
    rw [Nat.card_Icc]
    simp
  have hsum_odd : ∀ n : ℕ, (∑ j ∈ Finset.Icc 1 n, (2 * (j:ℝ) - 1)) = (n:ℝ)^2 := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
      push_cast
      ring
  have hquad_le : ∀ c : ℝ, 0 ≤ c → ∀ t ∈ Set.Icc (0:ℝ) 1,
      c * (t * (1 - t)) ≤ c / 4 := by
    intro c hc t ht
    have htq : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - (1/2))]
    nlinarith [mul_le_mul_of_nonneg_left htq hc]
  by_cases ha0 : a = 0
  · subst a
    have hbpos : 0 < b := by
      rcases hab with h | h
      · exact absurd h (lt_irrefl 0)
      · exact h
    obtain ⟨hz1, hz2, hz3, hz4⟩ := linear_pieces_zero b T k hT hbpos hk
    have hj1le : ∀ j ∈ Finset.Icc 1 k, (1:ℝ) ≤ (j:ℝ) := fun j hj => by
      exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hdenpos : ∀ j ∈ Finset.Icc 1 k, 0 < 2 * (j:ℝ) - 1 := by
      intro j hj
      have := hj1le j hj
      linarith
    have habsj : ∀ j ∈ Finset.Icc 1 k, ∀ t ∈ Set.Icc (0:ℝ) 1,
        |subCdf (linRate 0 b) T k j t - t|
          = (1 / (2 * (j:ℝ) - 1)) * (t * (1 - t)) := by
      intro j hj t ht
      rw [hz2 j hj t ht]
      have hd : (2 * (j:ℝ) - 1) ≠ 0 := ne_of_gt (hdenpos j hj)
      have hmain : t * (2 * (j:ℝ) - 2 + t) / (2 * (j:ℝ) - 1) - t
          = -((1 / (2 * (j:ℝ) - 1)) * (t * (1 - t))) := by
        field_simp
        ring
      rw [hmain, abs_neg]
      exact abs_of_nonneg (mul_nonneg (div_nonneg (by norm_num) (le_of_lt (hdenpos j hj)))
        (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)))
    have hgj : ∀ j ∈ Finset.Icc 1 k,
        IsGreatest ((fun t => |subCdf (linRate 0 b) T k j t - t|) '' Set.Icc (0:ℝ) 1)
          ((1 / (2 * (j:ℝ) - 1)) / 4) := by
      intro j hj
      constructor
      · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
        change |subCdf (linRate 0 b) T k j (1/2) - 1/2| = (1 / (2 * (j:ℝ) - 1)) / 4
        rw [habsj j hj (1/2) ⟨by norm_num, by norm_num⟩]
        ring
      · rintro y ⟨t, ht, rfl⟩
        change |subCdf (linRate 0 b) T k j t - t| ≤ (1 / (2 * (j:ℝ) - 1)) / 4
        rw [habsj j hj t ht]
        have hc : 0 ≤ 1 / (2 * (j:ℝ) - 1) :=
          div_nonneg (by norm_num) (le_of_lt (hdenpos j hj))
        exact hquad_le (1 / (2 * (j:ℝ) - 1)) hc t ht
    have hdegj : ∀ j ∈ Finset.Icc 1 k,
        degree (subCdf (linRate 0 b) T k j) = (1 / (2 * (j:ℝ) - 1)) / 4 := by
      intro j hj
      rw [degree]
      exact (hgj j hj).csSup_eq
    have hweightsum : (∑ j ∈ Finset.Icc 1 k, weight (linRate 0 b) T k j) = 1 := by
      rw [Finset.sum_congr rfl (fun j hj => hz3 j hj)]
      rw [← Finset.sum_div, hsum_odd k]
      exact div_self (pow_ne_zero 2 hk0)
    have hmixdiff : ∀ t ∈ Set.Icc (0:ℝ) 1,
        mixCdf (linRate 0 b) T k t - t
          = ∑ j ∈ Finset.Icc 1 k,
              weight (linRate 0 b) T k j * (subCdf (linRate 0 b) T k j t - t) := by
      intro t ht
      calc mixCdf (linRate 0 b) T k t - t
          = (∑ j ∈ Finset.Icc 1 k,
                weight (linRate 0 b) T k j * subCdf (linRate 0 b) T k j t)
              - (∑ j ∈ Finset.Icc 1 k, weight (linRate 0 b) T k j) * t := by
            rw [mixCdf, hweightsum, one_mul]
        _ = (∑ j ∈ Finset.Icc 1 k,
                weight (linRate 0 b) T k j * subCdf (linRate 0 b) T k j t)
              - (∑ j ∈ Finset.Icc 1 k, weight (linRate 0 b) T k j * t) := by
            rw [Finset.sum_mul]
        _ = ∑ j ∈ Finset.Icc 1 k,
              (weight (linRate 0 b) T k j * subCdf (linRate 0 b) T k j t
                - weight (linRate 0 b) T k j * t) := by
            rw [← Finset.sum_sub_distrib]
        _ = ∑ j ∈ Finset.Icc 1 k,
              weight (linRate 0 b) T k j * (subCdf (linRate 0 b) T k j t - t) :=
            Finset.sum_congr rfl (fun j hj => (mul_sub _ _ _).symm)
    have hw_nonneg : ∀ j ∈ Finset.Icc 1 k, 0 ≤ weight (linRate 0 b) T k j := by
      intro j hj
      rw [hz3 j hj]
      exact div_nonneg (by linarith [hj1le j hj]) (by positivity)
    have hmix_isg : IsGreatest
        ((fun t => |mixCdf (linRate 0 b) T k t - t|) '' Set.Icc (0:ℝ) 1)
        (∑ j ∈ Finset.Icc 1 k,
          weight (linRate 0 b) T k j * ((1 / (2 * (j:ℝ) - 1)) / 4)) := by
      constructor
      · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
        change |mixCdf (linRate 0 b) T k (1/2) - 1/2| = ∑ j ∈ Finset.Icc 1 k,
          weight (linRate 0 b) T k j * ((1 / (2 * (j:ℝ) - 1)) / 4)
        rw [hmixdiff (1/2) ⟨by norm_num, by norm_num⟩]
        have hhalf : ∀ j ∈ Finset.Icc 1 k,
            weight (linRate 0 b) T k j * (subCdf (linRate 0 b) T k j (1/2) - 1/2)
              = -(weight (linRate 0 b) T k j * ((1 / (2 * (j:ℝ) - 1)) / 4)) := by
          intro j hj
          rw [hz2 j hj (1/2) ⟨by norm_num, by norm_num⟩]
          have hd : (2 * (j:ℝ) - 1) ≠ 0 := ne_of_gt (hdenpos j hj)
          have hone : (1/2) * (2 * (j:ℝ) - 2 + 1/2) / (2 * (j:ℝ) - 1) - 1/2
              = -((1 / (2 * (j:ℝ) - 1)) / 4) := by
            field_simp
            ring
          rw [hone, mul_neg]
        rw [Finset.sum_congr rfl hhalf, Finset.sum_neg_distrib, abs_neg]
        exact abs_of_nonneg (Finset.sum_nonneg (fun j hj =>
          mul_nonneg (hw_nonneg j hj)
            (div_nonneg (div_nonneg (by norm_num) (le_of_lt (hdenpos j hj))) (by norm_num))))
      · rintro y ⟨t, ht, rfl⟩
        change |mixCdf (linRate 0 b) T k t - t| ≤ ∑ j ∈ Finset.Icc 1 k,
          weight (linRate 0 b) T k j * ((1 / (2 * (j:ℝ) - 1)) / 4)
        rw [hmixdiff t ht]
        calc |∑ j ∈ Finset.Icc 1 k,
                weight (linRate 0 b) T k j * (subCdf (linRate 0 b) T k j t - t)|
            ≤ ∑ j ∈ Finset.Icc 1 k,
                |weight (linRate 0 b) T k j * (subCdf (linRate 0 b) T k j t - t)| :=
              Finset.abs_sum_le_sum_abs
                (fun j => weight (linRate 0 b) T k j * (subCdf (linRate 0 b) T k j t - t))
                (Finset.Icc 1 k)
          _ = ∑ j ∈ Finset.Icc 1 k,
                weight (linRate 0 b) T k j * |subCdf (linRate 0 b) T k j t - t| := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [abs_mul, abs_of_nonneg (hw_nonneg j hj)]
          _ ≤ ∑ j ∈ Finset.Icc 1 k,
                weight (linRate 0 b) T k j * ((1 / (2 * (j:ℝ) - 1)) / 4) := by
              apply Finset.sum_le_sum
              intro j hj
              apply mul_le_mul_of_nonneg_left _ (hw_nonneg j hj)
              rw [habsj j hj t ht]
              have hc : 0 ≤ 1 / (2 * (j:ℝ) - 1) :=
                div_nonneg (by norm_num) (le_of_lt (hdenpos j hj))
              exact hquad_le (1 / (2 * (j:ℝ) - 1)) hc t ht
    have hdegmix : degree (mixCdf (linRate 0 b) T k)
        = ∑ j ∈ Finset.Icc 1 k,
            weight (linRate 0 b) T k j * ((1 / (2 * (j:ℝ) - 1)) / 4) := by
      rw [degree]
      exact hmix_isg.csSup_eq
    refine ⟨?_, ?_, ?_⟩
    · rw [hdegmix]
      exact hmix_isg
    · intro j hj
      rw [hdegj j hj]
      exact hgj j hj
    · rw [hdegmix]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hdegj j hj]
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hD : 0 ≤ (b / a) * T := mul_nonneg (div_nonneg hb ha) hT.le
    have h2D : 0 < 2 + (b / a) * T := by linarith
    have hpos := fun j hj => linear_pieces_pos a b T k hT hapos hb hk j hj
    have hj1le : ∀ j ∈ Finset.Icc 1 k, (1:ℝ) ≤ (j:ℝ) := fun j hj => by
      exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hdenpos : ∀ j ∈ Finset.Icc 1 k,
        0 < 2 * (k:ℝ) + (2 * (j:ℝ) - 1) * (b / a) * T := by
      intro j hj
      have h2j : (0:ℝ) ≤ 2 * (j:ℝ) - 1 := by linarith [hj1le j hj]
      have hprod : 0 ≤ (2 * (j:ℝ) - 1) * (b / a) * T :=
        mul_nonneg (mul_nonneg h2j (div_nonneg hb ha)) hT.le
      have hk2 : (0:ℝ) < 2 * k := by
        have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
        linarith
      linarith
    have habsj : ∀ j ∈ Finset.Icc 1 k, ∀ t ∈ Set.Icc (0:ℝ) 1,
        |subCdf (linRate a b) T k j t - t|
          = ((b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T))
              * (t * (1 - t)) := by
      intro j hj t ht
      rw [(hpos j hj).2.1 t ht]
      have hd : (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T) ≠ 0 :=
        ne_of_gt (hdenpos j hj)
      have hmain : t * (2 * k + (2 * (j:ℝ) - 2 + t) * (b / a) * T)
            / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T) - t
          = -(((b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T))
              * (t * (1 - t))) := by
        rw [div_mul_eq_mul_div, ← neg_div, eq_div_iff_mul_eq hd]
        rw [sub_mul, div_mul_cancel₀ _ hd]
        ring
      rw [hmain, abs_neg]
      exact abs_of_nonneg (mul_nonneg
        (div_nonneg hD (le_of_lt (hdenpos j hj)))
        (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)))
    have hgj : ∀ j ∈ Finset.Icc 1 k,
        IsGreatest ((fun t => |subCdf (linRate a b) T k j t - t|) '' Set.Icc (0:ℝ) 1)
          (((b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T)) / 4) := by
      intro j hj
      constructor
      · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
        change |subCdf (linRate a b) T k j (1/2) - 1/2| = ((b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T)) / 4
        rw [habsj j hj (1/2) ⟨by norm_num, by norm_num⟩]
        ring
      · rintro y ⟨t, ht, rfl⟩
        change |subCdf (linRate a b) T k j t - t| ≤ ((b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T)) / 4
        rw [habsj j hj t ht]
        have hc : 0 ≤ (b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T) :=
          div_nonneg hD (le_of_lt (hdenpos j hj))
        exact hquad_le _ hc t ht
    have hdegj : ∀ j ∈ Finset.Icc 1 k,
        degree (subCdf (linRate a b) T k j)
          = ((b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T)) / 4 := by
      intro j hj
      rw [degree]
      exact (hgj j hj).csSup_eq
    have hweightsum : (∑ j ∈ Finset.Icc 1 k, weight (linRate a b) T k j) = 1 := by
      rw [Finset.sum_congr rfl (fun j hj => (hpos j hj).2.2.1)]
      rw [← Finset.sum_div]
      have hnum2 : (∑ j ∈ Finset.Icc 1 k, (2 * (j:ℝ) - 1) * (b / a) * T)
          = (b / a) * T * (k:ℝ)^2 := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, hsum_odd k]
        ring
      have hnum : (∑ j ∈ Finset.Icc 1 k,
            (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T))
          = (k:ℝ)^2 * (2 + (b / a) * T) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
        rw [hnum2]
        ring
      rw [hnum]
      exact div_self (mul_ne_zero (pow_ne_zero 2 hk0) (ne_of_gt h2D))
    have hmixdiff : ∀ t ∈ Set.Icc (0:ℝ) 1,
        mixCdf (linRate a b) T k t - t
          = ∑ j ∈ Finset.Icc 1 k,
              weight (linRate a b) T k j * (subCdf (linRate a b) T k j t - t) := by
      intro t ht
      calc mixCdf (linRate a b) T k t - t
          = (∑ j ∈ Finset.Icc 1 k,
                weight (linRate a b) T k j * subCdf (linRate a b) T k j t)
              - (∑ j ∈ Finset.Icc 1 k, weight (linRate a b) T k j) * t := by
            rw [mixCdf, hweightsum, one_mul]
        _ = (∑ j ∈ Finset.Icc 1 k,
                weight (linRate a b) T k j * subCdf (linRate a b) T k j t)
              - (∑ j ∈ Finset.Icc 1 k, weight (linRate a b) T k j * t) := by
            rw [Finset.sum_mul]
        _ = ∑ j ∈ Finset.Icc 1 k,
              (weight (linRate a b) T k j * subCdf (linRate a b) T k j t
                - weight (linRate a b) T k j * t) := by
            rw [← Finset.sum_sub_distrib]
        _ = ∑ j ∈ Finset.Icc 1 k,
              weight (linRate a b) T k j * (subCdf (linRate a b) T k j t - t) :=
            Finset.sum_congr rfl (fun j hj => (mul_sub _ _ _).symm)
    have hw_nonneg : ∀ j ∈ Finset.Icc 1 k, 0 ≤ weight (linRate a b) T k j := by
      intro j hj
      rw [(hpos j hj).2.2.1]
      exact div_nonneg (le_of_lt (hdenpos j hj))
        (mul_nonneg (sq_nonneg _) (by linarith [hD]))
    have hmix_isg : IsGreatest
        ((fun t => |mixCdf (linRate a b) T k t - t|) '' Set.Icc (0:ℝ) 1)
        (∑ j ∈ Finset.Icc 1 k,
          weight (linRate a b) T k j
            * (((b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T)) / 4)) := by
      constructor
      · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
        change |mixCdf (linRate a b) T k (1/2) - 1/2| = ∑ j ∈ Finset.Icc 1 k,
          weight (linRate a b) T k j
            * (((b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T)) / 4)
        rw [hmixdiff (1/2) ⟨by norm_num, by norm_num⟩]
        have hhalf : ∀ j ∈ Finset.Icc 1 k,
            weight (linRate a b) T k j * (subCdf (linRate a b) T k j (1/2) - 1/2)
              = -(weight (linRate a b) T k j
                  * (((b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T)) / 4)) := by
          intro j hj
          rw [(hpos j hj).2.1 (1/2) ⟨by norm_num, by norm_num⟩]
          have hd : (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T) ≠ 0 :=
            ne_of_gt (hdenpos j hj)
          have hone : (1/2) * (2 * k + (2 * (j:ℝ) - 2 + 1/2) * (b / a) * T)
                / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T) - 1/2
              = -(((b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T)) / 4) := by
            rw [show -(((b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T)) / 4)
                = (-((b / a) * T / 4)) / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T) by ring]
            rw [eq_div_iff_mul_eq hd]
            rw [sub_mul, div_mul_cancel₀ _ hd]
            ring
          rw [hone, mul_neg]
        rw [Finset.sum_congr rfl hhalf, Finset.sum_neg_distrib, abs_neg]
        exact abs_of_nonneg (Finset.sum_nonneg (fun j hj =>
          mul_nonneg (hw_nonneg j hj)
            (div_nonneg (div_nonneg hD (le_of_lt (hdenpos j hj))) (by norm_num))))
      · rintro y ⟨t, ht, rfl⟩
        change |mixCdf (linRate a b) T k t - t| ≤ ∑ j ∈ Finset.Icc 1 k,
          weight (linRate a b) T k j
            * (((b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T)) / 4)
        rw [hmixdiff t ht]
        calc |∑ j ∈ Finset.Icc 1 k,
                weight (linRate a b) T k j * (subCdf (linRate a b) T k j t - t)|
            ≤ ∑ j ∈ Finset.Icc 1 k,
                |weight (linRate a b) T k j * (subCdf (linRate a b) T k j t - t)| :=
              Finset.abs_sum_le_sum_abs
                (fun j => weight (linRate a b) T k j * (subCdf (linRate a b) T k j t - t))
                (Finset.Icc 1 k)
          _ = ∑ j ∈ Finset.Icc 1 k,
                weight (linRate a b) T k j * |subCdf (linRate a b) T k j t - t| := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [abs_mul, abs_of_nonneg (hw_nonneg j hj)]
          _ ≤ ∑ j ∈ Finset.Icc 1 k,
                weight (linRate a b) T k j
                  * (((b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T)) / 4) := by
              apply Finset.sum_le_sum
              intro j hj
              apply mul_le_mul_of_nonneg_left _ (hw_nonneg j hj)
              rw [habsj j hj t ht]
              have hc : 0 ≤ (b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T) :=
                div_nonneg hD (le_of_lt (hdenpos j hj))
              exact hquad_le _ hc t ht
    have hdegmix : degree (mixCdf (linRate a b) T k)
        = ∑ j ∈ Finset.Icc 1 k,
            weight (linRate a b) T k j
              * (((b / a) * T / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T)) / 4) := by
      rw [degree]
      exact hmix_isg.csSup_eq
    refine ⟨?_, ?_, ?_⟩
    · rw [hdegmix]
      exact hmix_isg
    · intro j hj
      rw [hdegj j hj]
      exact hgj j hj
    · rw [hdegmix]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hdegj j hj]
