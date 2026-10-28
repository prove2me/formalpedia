-- Prove2me | solution 1 for MarketFreeze.Hetero.eq_13_nash_price
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:50:04.588141+00:00
-- url     : https://prove2.me/submissions/4339a2bc-182f-4a2b-a955-7532a44b8176

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace Aux_MF_eq13

lemma key (D β γ a b : ℝ) (hD : 0 < D) (hβ : 0 < β) (hγ : 0 < γ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ β * b ^ γ = (β * D) ^ β * (γ * D) ^ γ * ((a / (β * D)) ^ β * (b / (γ * D)) ^ γ) := by
  have h1 : 0 < β * D := mul_pos hβ hD
  have h2 : 0 < γ * D := mul_pos hγ hD
  rw [Real.div_rpow ha h1.le, Real.div_rpow hb h2.le]
  have h3 : 0 < (β * D) ^ β := Real.rpow_pos_of_pos h1 _
  have h4 : 0 < (γ * D) ^ γ := Real.rpow_pos_of_pos h2 _
  field_simp

end Aux_MF_eq13

open MarketFreeze.Hetero in
theorem solution (P : Params) (hXI : P.I < P.X)
    (n : ℝ) (hn : 0 ≤ n) :
    price P n ∈ Set.Icc P.I P.X ∧
    (∀ p ∈ Set.Icc P.I P.X, nashProduct P n p ≤ nashProduct P n (price P n)) ∧
    (∀ p ∈ Set.Icc P.I P.X,
      nashProduct P n p = nashProduct P n (price P n) → p = price P n) ∧
    StrictMonoOn (price P) (Set.Ici 0) := by
  have hD : 0 < P.X - P.I := by linarith
  have hβdef : beta n = 1 / (1 + n) := rfl
  have hβ0 : 0 < beta n := by rw [hβdef]; positivity
  have hβ1 : beta n ≤ 1 := by rw [hβdef, div_le_one (by linarith)]; linarith
  have hXp : P.X - price P n = beta n * (P.X - P.I) := by rw [hβdef]; unfold price; ring
  have hpI : price P n - P.I = (1 - beta n) * (P.X - P.I) := by rw [hβdef]; unfold price; ring
  have hmono : StrictMonoOn (price P) (Set.Ici 0) := by
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    unfold price
    have : (P.X - P.I) / (1 + y) < (P.X - P.I) / (1 + x) :=
      div_lt_div_of_pos_left hD (by linarith) (by linarith)
    linarith
  have hmem : price P n ∈ Set.Icc P.I P.X := by
    constructor
    · have : 0 ≤ (1 - beta n) * (P.X - P.I) := mul_nonneg (by linarith) hD.le
      linarith
    · have : 0 ≤ beta n * (P.X - P.I) := mul_nonneg hβ0.le hD.le
      linarith
  refine ⟨hmem, ?_, ?_, hmono⟩
  · rcases hn.eq_or_lt with h | h
    · subst h
      have hb : beta 0 = 1 := by rw [hβdef]; norm_num
      intro p hp
      unfold nashProduct
      rw [hb]
      simp only [sub_self, Real.rpow_one, Real.rpow_zero, mul_one]
      have : price P 0 = P.I := by unfold price; ring
      rw [this]; linarith [hp.1]
    · intro p hp
      have hγ : 0 < 1 - beta n := by
        rw [hβdef, sub_pos, div_lt_one (by linarith)]; linarith
      have hC : 0 < (beta n * (P.X - P.I)) ^ beta n * ((1 - beta n) * (P.X - P.I)) ^ (1 - beta n) := by
        apply mul_pos <;> apply Real.rpow_pos_of_pos <;> positivity
      unfold nashProduct
      rw [hXp, hpI, Aux_MF_eq13.key (P.X - P.I) (beta n) (1 - beta n) (P.X - p) (p - P.I) hD hβ0 hγ
        (by linarith [hp.2]) (by linarith [hp.1])]
      have hg := Real.geom_mean_le_arith_mean2_weighted hβ0.le hγ.le
        (div_nonneg (by linarith [hp.2] : (0:ℝ) ≤ P.X - p) (mul_pos hβ0 hD).le)
        (div_nonneg (by linarith [hp.1] : (0:ℝ) ≤ p - P.I) (mul_pos hγ hD).le) (by ring)
      have hsum : beta n * ((P.X - p) / (beta n * (P.X - P.I))) +
          (1 - beta n) * ((p - P.I) / ((1 - beta n) * (P.X - P.I))) = 1 := by
        have := hβ0.ne'; have := hγ.ne'; have := hD.ne'
        field_simp
        ring
      rw [hsum] at hg
      calc _ ≤ (beta n * (P.X - P.I)) ^ beta n * ((1 - beta n) * (P.X - P.I)) ^ (1 - beta n) * 1 :=
            mul_le_mul_of_nonneg_left hg hC.le
        _ = _ := mul_one _
  · rcases hn.eq_or_lt with h | h
    · subst h
      have hb : beta 0 = 1 := by rw [hβdef]; norm_num
      intro p hp heq
      unfold nashProduct at heq
      rw [hb] at heq
      simp only [sub_self, Real.rpow_one, Real.rpow_zero, mul_one] at heq
      linarith
    · intro p hp heq
      have hγ : 0 < 1 - beta n := by
        rw [hβdef, sub_pos, div_lt_one (by linarith)]; linarith
      have hC : 0 < (beta n * (P.X - P.I)) ^ beta n * ((1 - beta n) * (P.X - P.I)) ^ (1 - beta n) := by
        apply mul_pos <;> apply Real.rpow_pos_of_pos <;> positivity
      unfold nashProduct at heq
      rw [hXp, hpI, Aux_MF_eq13.key (P.X - P.I) (beta n) (1 - beta n) (P.X - p) (p - P.I) hD hβ0 hγ
        (by linarith [hp.2]) (by linarith [hp.1])] at heq
      have hu0 : (0:ℝ) ≤ (P.X - p) / (beta n * (P.X - P.I)) :=
        div_nonneg (by linarith [hp.2]) (mul_pos hβ0 hD).le
      have hw0 : (0:ℝ) ≤ (p - P.I) / ((1 - beta n) * (P.X - P.I)) :=
        div_nonneg (by linarith [hp.1]) (mul_pos hγ hD).le
      have hsum : beta n * ((P.X - p) / (beta n * (P.X - P.I))) +
          (1 - beta n) * ((p - P.I) / ((1 - beta n) * (P.X - P.I))) = 1 := by
        have := hβ0.ne'; have := hγ.ne'; have := hD.ne'
        field_simp
        ring
      have hg1 : ((P.X - p) / (beta n * (P.X - P.I))) ^ beta n *
          ((p - P.I) / ((1 - beta n) * (P.X - P.I))) ^ (1 - beta n) = 1 := by
        have := heq
        nth_rewrite 2 [← mul_one ((beta n * (P.X - P.I)) ^ beta n * ((1 - beta n) * (P.X - P.I)) ^ (1 - beta n))] at this
        exact mul_left_cancel₀ hC.ne' this
      have huw := (Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos hβ0 hγ hu0 hw0 (by ring)).mp
        (hg1.trans hsum.symm)
      rw [← huw] at hsum
      have hu1 : (P.X - p) / (beta n * (P.X - P.I)) = 1 := by linarith
      rw [div_eq_one_iff_eq (mul_pos hβ0 hD).ne'] at hu1
      linarith
