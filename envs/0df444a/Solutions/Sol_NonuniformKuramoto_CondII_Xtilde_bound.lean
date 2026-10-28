-- Prove2me | solution 1 for NonuniformKuramoto.CondII.Xtilde_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:37:51.082211+00:00
-- url     : https://prove2.me/submissions/cb2569eb-42e6-44ee-81eb-0a4337c43263

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
open Matrix

namespace Aux_NonuniformKuramoto_CondII_Xtilde_bound
open NonuniformKuramoto.CondII

theorem Hmul {n : ℕ} (x : Fin n → ℝ) (p : Pairs n) :
    (incH n *ᵥ x) p = x p.1.2 - x p.1.1 := by
  have hne : p.1.2 ≠ p.1.1 := ne_of_gt p.2
  simp only [mulVec, dotProduct, incH]
  rw [Fintype.sum_eq_add p.1.2 p.1.1 hne]
  · rw [if_pos rfl, if_neg (Ne.symm hne), if_pos rfl]; ring
  · intro c hc
    rw [if_neg hc.1, if_neg hc.2, zero_mul]

theorem pair_sum {n : ℕ} (g : Fin n → Fin n → ℝ) :
    ∑ p : Pairs n, g p.1.1 p.1.2 = ∑ a, ∑ b, if a < b then g a b else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2))
    (p := fun x : Fin n × Fin n => x.1 < x.2) (by simp) (fun x => g x.1 x.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem symm_split {n : ℕ} (T : Fin n → Fin n → ℝ) (hT : ∀ i j, T i j = T j i) :
    ∑ i, ∑ j, T i j = ∑ i, T i i + 2 * ∑ i, ∑ j, if i < j then T i j else 0 := by
  have h1 : ∀ i j, T i j = (if j = i then T i j else 0) + (if i < j then T i j else 0) +
      (if j < i then T i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_gt h, not_lt_of_gt h]
    · subst h; simp
    · simp [h, ne_of_lt h, not_lt_of_gt h]
  have h2 : ∀ i, ∑ j, T i j = T i i + (∑ j, if i < j then T i j else 0) +
      ∑ j, if j < i then T i j else 0 := by
    intro i
    rw [Finset.sum_congr rfl fun j _ => h1 i j, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq']
    simp
  have h3 : ∑ i, ∑ j, (if j < i then T i j else 0) = ∑ i, ∑ j, (if i < j then T i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [hT]
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib, Finset.sum_add_distrib, h3]
  ring

end Aux_NonuniformKuramoto_CondII_Xtilde_bound

namespace Aux_NonuniformKuramoto_CondII_Xtilde_bound
open NonuniformKuramoto.CondII

theorem pair_sq {n : ℕ} (x : Fin n → ℝ) :
    ∑ a, ∑ b, (if a < b then (x b - x a) ^ 2 else 0) = (n : ℝ) * ∑ i, x i ^ 2 - (∑ i, x i) ^ 2 := by
  have hs := symm_split (fun a b => (x b - x a) ^ 2) (fun a b => by ring)
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, zero_add] at hs
  have hfull : ∑ a, ∑ b, (x b - x a) ^ 2 = 2 * ((n : ℝ) * ∑ i, x i ^ 2) - 2 * (∑ i, x i) ^ 2 := by
    have e : ∀ a b, (x b - x a) ^ 2 = x b ^ 2 + x a ^ 2 - 2 * (x a * x b) := fun a b => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul]
    ring
  linarith

end Aux_NonuniformKuramoto_CondII_Xtilde_bound

open NonuniformKuramoto.CondII Aux_NonuniformKuramoto_CondII_Xtilde_bound in
theorem solution {n : ℕ} (D : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hyp : StandingHyp D P ϕ) (θ : Fin n → ℝ) :
    normH (lossyX D P ϕ θ) ≤ Xtilde D P ϕ := by
  set x := lossyX D P ϕ θ with hx
  set v := lossyVec D P ϕ with hv
  have hc : ∀ i j, 0 ≤ P i j / D i * Real.sin (ϕ i j) := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [hyp.P_diag]; simp
    · refine mul_nonneg (div_nonneg (hyp.P_nonneg i j hij) (hyp.D_pos i).le) ?_
      apply Real.sin_nonneg_of_nonneg_of_le_pi (hyp.ϕ_nonneg i j hij)
      linarith [hyp.ϕ_lt i j hij, Real.pi_pos]
  have hxv : ∀ i, |x i| ≤ v i := by
    intro i
    simp only [hx, hv, lossyX, lossyVec]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (hc i j)]
    calc P i j / D i * Real.sin (ϕ i j) * |Real.cos (θ i - θ j)|
        ≤ P i j / D i * Real.sin (ϕ i j) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hc i j)
      _ = P i j / D i * Real.sin (ϕ i j) := mul_one _
  have hsq : ∀ i, x i ^ 2 ≤ v i ^ 2 := by
    intro i
    have := hxv i
    have h0 : 0 ≤ |x i| := abs_nonneg _
    nlinarith [sq_abs (x i)]
  unfold normH Xtilde euclNorm
  have hpair : ∑ p : Pairs n, (incH n *ᵥ x) p ^ 2 = (n : ℝ) * ∑ i, x i ^ 2 - (∑ i, x i) ^ 2 := by
    rw [← pair_sq]
    rw [← pair_sum (fun a b => (x b - x a) ^ 2)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Hmul]
  rw [hpair, ← Real.sqrt_mul (Nat.cast_nonneg n)]
  apply Real.sqrt_le_sqrt
  have h1 : ∑ i, x i ^ 2 ≤ ∑ i, v i ^ 2 := Finset.sum_le_sum fun i _ => hsq i
  have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [sq_nonneg (∑ i, x i), mul_le_mul_of_nonneg_left h1 h2]
