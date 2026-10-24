-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translation_scalar_weighted_bound_core_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:36:39.672967+00:00
-- url     : https://prove2.me/submissions/2b0abd07-307c-4492-87ce-c8c88708f135

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Mathlib.Data.Fintype.BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open scoped BigOperators

namespace S105TS

def Good (P : PowerSeries ℂ) (L : ℕ) : Prop :=
  (∀ n, ‖PowerSeries.coeff n P‖ ≤ (2 : ℝ) ^ n) ∧ ∀ n, n < L → PowerSeries.coeff n P = 0

lemma good_one : Good 1 0 := by
  refine ⟨fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
  rw [PowerSeries.coeff_one]
  split_ifs <;> simp [one_le_pow₀]

lemma coeff_tail (T n : ℕ) :
    PowerSeries.coeff n (tail T) = if n < T then 0 else -PowerSeries.coeff n (PowerSeries.log ℂ) := by
  unfold tail
  rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs <;> ring

lemma norm_coeff_log (n : ℕ) : ‖PowerSeries.coeff n (PowerSeries.log ℂ)‖ ≤ 1 := by
  rw [PowerSeries.coeff_log]
  split_ifs with h
  · simp
  · rw [eq_ratCast, Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast,
      norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
    have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h
    rw [div_le_one (by linarith)]; exact this

lemma tail_bound (T : ℕ) (hT : 1 ≤ T) (n : ℕ) :
    ‖PowerSeries.coeff n (tail T)‖ ≤ if n = 0 then 0 else 1 := by
  rw [coeff_tail]
  split_ifs with h1 h2
  · simp
  · simp
  · omega
  · rw [norm_neg]; exact norm_coeff_log n

lemma geom (n : ℕ) : ∑ k ∈ Finset.range n, (2 : ℝ) ^ k ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : (0 : ℝ) ≤ 2 ^ n := by positivity
    linarith

lemma good_mul (P : PowerSeries ℂ) (L T : ℕ) (hT : 1 ≤ T) (hP : Good P L) :
    Good (P * tail T) (L + T) := by
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_range_succ]
    have hlast : ‖PowerSeries.coeff n P * PowerSeries.coeff (n - n) (tail T)‖ = 0 := by
      have := tail_bound T hT (n - n)
      simp only [Nat.sub_self, if_true] at this
      rw [norm_mul, Nat.sub_self, norm_le_zero_iff.1 this]; simp
    simp only at hlast ⊢
    rw [hlast, add_zero]
    refine le_trans (Finset.sum_le_sum fun k hk => ?_) (geom n)
    rw [norm_mul]
    have h1 := hP.1 k
    have h2 := (tail_bound T hT (n - k)).trans (by split_ifs <;> norm_num : (if n - k = 0 then (0:ℝ) else 1) ≤ 1)
    calc ‖PowerSeries.coeff k P‖ * ‖PowerSeries.coeff (n - k) (tail T)‖ ≤ 2 ^ k * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 2 ^ k := mul_one _
  · rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    by_cases h : p.1 < L
    · rw [hP.2 _ h, zero_mul]
    · rw [coeff_tail, if_pos (by omega), mul_zero]

lemma good_pow (P : PowerSeries ℂ) (L T d : ℕ) (hT : 1 ≤ T) (hP : Good P L) :
    Good (P * tail T ^ d) (L + d * T) := by
  induction d with
  | zero => simpa using hP
  | succ d ih =>
    have := good_mul _ _ T hT ih
    rw [pow_succ, ← mul_assoc]
    convert this using 1; ring

lemma good_prod {m : ℕ} (s : Finset (Fin m)) (T : Fin m → ℕ) (d : Fin m → ℕ) (hT : ∀ i, 1 ≤ T i) :
    Good (∏ i ∈ s, tail (T i) ^ d i) (∑ i ∈ s, d i * T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, mul_comm, add_comm]
    exact good_pow _ _ _ _ (hT j) ih

end S105TS

theorem solution {m : ℕ} (ε : Fin m → ℂ) (T : Fin m → ℕ) (β a : Fin m → ℕ) (δ : ∀ i : Fin m, Fin (a i - β i + 1)) (k : ℕ) (w : Fin m → ℝ) (C ν H ws v F : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν) (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F) (hw : ∀ i, ws ≤ w i) (ha : ∑ i : Fin m, w i * (a i : ℝ) ≤ H) (hk : (k : ℝ) ≤ H / v) (hT : ∀ i, 1 ≤ T i) (hTw : ∀ i, F * w i ≤ v * T i) (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) : ‖((∏ i, (((a i).choose (β i) * (a i - β i).choose (δ i) : ℕ) : ℂ)) * (∏ i, ε i ^ (a i - β i - (δ i : ℕ))) * PowerSeries.coeff k (∏ i, MinorTranslationData.tail (T i) ^ (δ i : ℕ)))‖ ≤ Real.exp (-ν * ((∑ i : Fin m, w i * (a i : ℝ)) - (∑ i : Fin m, w i * (β i : ℝ))) + H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by
  have hG := S105TS.good_prod Finset.univ T (fun i => (δ i : ℕ)) hT
  by_cases hk0 : PowerSeries.coeff k (∏ i, MinorTranslationData.tail (T i) ^ (δ i : ℕ)) = 0
  · rw [hk0, mul_zero, norm_zero]; exact (Real.exp_pos _).le
  have hkT : ∑ i, (δ i : ℕ) * T i ≤ k := by
    by_contra h; exact hk0 (hG.2 k (by omega))
  set e : Fin m → ℕ := fun i => a i - β i - (δ i : ℕ) with he
  set SA : ℝ := ∑ i, (a i : ℝ) with hSA
  -- norm bounds
  have N1 : ‖(∏ i, (((a i).choose (β i) * (a i - β i).choose (δ i) : ℕ) : ℂ))‖
      ≤ Real.exp (Real.log 4 * SA) := by
    rw [← Nat.cast_prod, Complex.norm_natCast]
    have h4 : (∏ i, ((a i).choose (β i) * (a i - β i).choose (δ i))) ≤ ∏ i, 4 ^ (a i) := by
      apply Finset.prod_le_prod' 
      intro i _
      have c1 := Nat.choose_le_two_pow (a i) (β i)
      have c2 := Nat.choose_le_two_pow (a i - β i) (δ i)
      have c3 : 2 ^ (a i - β i) ≤ 2 ^ (a i) := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
      calc (a i).choose (β i) * (a i - β i).choose (δ i) ≤ 2 ^ a i * 2 ^ a i :=
            Nat.mul_le_mul c1 (c2.trans c3)
        _ = 4 ^ a i := by rw [← mul_pow]; norm_num
    have := (Nat.cast_le (α := ℝ)).2 h4
    refine this.trans (le_of_eq ?_)
    rw [Finset.prod_pow_eq_pow_sum, Nat.cast_pow, hSA, ← Nat.cast_sum]
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have N2 : ‖∏ i, ε i ^ e i‖ ≤ Real.exp (∑ i, (e i : ℝ) * (C - ν * w i)) := by
    rw [norm_prod, Real.exp_sum]
    apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
    intro i _
    rw [norm_pow, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (hε i) _
  have N3 : ‖PowerSeries.coeff k (∏ i, MinorTranslationData.tail (T i) ^ (δ i : ℕ))‖
      ≤ Real.exp (k * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    exact hG.1 k
  rw [norm_mul, norm_mul]
  have hprod := mul_le_mul (mul_le_mul N1 N2 (norm_nonneg _) (Real.exp_pos _).le) N3
    (norm_nonneg _) (by positivity)
  refine hprod.trans ?_
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  -- linear arithmetic
  have hw0 : ∀ i, 0 ≤ w i := fun i => hws.le.trans (hw i)
  have fA : ws * SA ≤ H := by
    rw [hSA, Finset.mul_sum]
    exact (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _)).trans ha
  have hA : SA ≤ H / ws := by rw [le_div_iff₀ hws]; linarith
  have hkT' : (∑ i, ((δ i : ℕ) : ℝ) * (T i : ℝ)) ≤ k := by exact_mod_cast hkT
  have fB : F * ∑ i, w i * ((δ i : ℕ) : ℝ) ≤ v * k := by
    rw [Finset.mul_sum]
    calc ∑ i, F * (w i * ((δ i : ℕ) : ℝ)) ≤ ∑ i, v * (((δ i : ℕ) : ℝ) * (T i : ℝ)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := mul_le_mul_of_nonneg_right (hTw i) (Nat.cast_nonneg ((δ i : ℕ)))
          nlinarith
      _ = v * ∑ i, (((δ i : ℕ) : ℝ) * (T i : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ v * k := mul_le_mul_of_nonneg_left hkT' hv.le
  have hkv : (k : ℝ) * v ≤ H := by rw [le_div_iff₀ hv] at hk; linarith
  have hB : (∑ i, w i * ((δ i : ℕ) : ℝ)) ≤ H / F := by rw [le_div_iff₀ hF]; linarith
  have he1 : ∀ i, (e i : ℝ) ≤ a i := fun i => by
    have : e i ≤ a i := by simp only [he]; omega
    exact_mod_cast this
  have he2 : ∀ i, (a i : ℝ) - β i - ((δ i : ℕ) : ℝ) ≤ e i := fun i => by
    have : a i ≤ e i + β i + (δ i : ℕ) := by simp only [he]; omega
    have : (a i : ℝ) ≤ e i + β i + ((δ i : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hCe : (∑ i, (e i : ℝ)) ≤ SA := Finset.sum_le_sum fun i _ => he1 i
  have hwe : (∑ i, w i * (a i : ℝ)) - (∑ i, w i * (β i : ℝ)) - (∑ i, w i * ((δ i : ℕ) : ℝ))
      ≤ ∑ i, w i * (e i : ℝ) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => by
      have := mul_le_mul_of_nonneg_left (he2 i) (hw0 i); linarith
  have hsplit : (∑ i, (e i : ℝ) * (C - ν * w i)) = C * (∑ i, (e i : ℝ)) - ν * ∑ i, w i * (e i : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hRHS : H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws)
      = ν * (H / F) + Real.log 2 * (H / v) + Real.log 4 * (H / ws) + C * (H / ws) := by
    field_simp; ring
  rw [hsplit, hRHS]
  have l4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have l2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have i1 := mul_le_mul_of_nonneg_left hA l4
  have i2 := mul_le_mul_of_nonneg_left (hCe.trans hA) hC
  have i3 := mul_le_mul_of_nonneg_left hwe hν
  have i4 := mul_le_mul_of_nonneg_left hB hν
  have i5 := mul_le_mul_of_nonneg_right hk l2
  nlinarith
