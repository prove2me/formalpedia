-- Prove2me | solution 1 for Helfgott.odd_floor_two_power_sum_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T05:27:21.300037+00:00
-- url     : https://prove2.me/submissions/ebb0ddaa-6e5f-4cbd-b2a9-4568759f329e

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Semifield

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
open Finset Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma odd_power_step (M : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ((2*(M+1)+1 : ℕ) : ℝ)^(a-1) ≤
      ((((2*(M+1)+1 : ℕ) : ℝ)^a)-((2*M+1 : ℕ) : ℝ)^a)/(2*a) := by
  let l : ℝ := (2*M+1 : ℕ)
  let r : ℝ := (2*(M+1)+1 : ℕ)
  have hl : 0 < l := by dsimp [l];positivity
  have hlr : l ≤ r := by dsimp [l,r];push_cast;nlinarith
  have hr : 0 < r := lt_of_lt_of_le hl hlr
  have hi := intervalIntegral.integral_mono_on hlr
    (intervalIntegrable_const (c := r^(a-1)))
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < a-1))
    (fun x hx => Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hl hx.1) hx.2 (by linarith : a-1 ≤ 0))
  have heval : (∫ x in l..r,x^(a-1))=(r^a-l^a)/a := by
    rw [integral_rpow (Or.inl (by linarith : -1 < a-1))]
    simp only [sub_add_cancel]
  rw [heval,intervalIntegral.integral_const] at hi
  have hlen : r-l=2 := by dsimp [l,r];push_cast;ring
  rw [hlen] at hi
  simp only [smul_eq_mul] at hi
  apply (le_div_iff₀ (by positivity : 0 < 2*a)).mpr
  have hh := (le_div_iff₀ ha).mp hi
  change r^(a-1)*(2*a) ≤ r^a-l^a
  nlinarith

theorem odd_progression_power_sum_upper (M : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∑ j∈range (M+1), ((2*j+1 : ℕ) : ℝ)^(a-1)) ≤
      1+((((2*M+1 : ℕ) : ℝ)^a)-1)/(2*a) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hs := odd_power_step M a ha ha1
    have h := add_le_add ih hs
    apply h.trans_eq
    push_cast
    ring

theorem odd_power_sum_upper (N : ℕ) (a : ℝ) (hN : 1 ≤ N) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∑ k∈Icc 1 N,if Nat.Coprime k 2 then (k : ℝ)^(a-1) else 0) ≤
      1+((N : ℝ)^a-1)/(2*a) := by
  let M : ℕ := (N-1)/2
  have hMN : 2*M+1 ≤ N := by dsimp only [M];omega
  have hNM : N ≤ 2*M+2 := by dsimp only [M];omega
  have heq : (∑ j∈range (M+1),((2*j+1 : ℕ) : ℝ)^(a-1))=
      ∑ k∈Icc 1 N,if Nat.Coprime k 2 then (k : ℝ)^(a-1) else 0 := by
    rw [←Finset.sum_filter]
    apply Finset.sum_bij (fun j _ => 2*j+1)
    · intro j hj
      have hjM : j ≤ M := by
        have := mem_range.mp hj
        omega
      apply mem_filter.mpr
      constructor
      · apply mem_Icc.mpr
        omega
      · rw [Nat.coprime_two_right]
        exact ⟨j,by omega⟩
    · intro i hi j hj he
      omega
    · intro k hk
      have hkN := (mem_Icc.mp (mem_filter.mp hk).1).2
      rcases (Nat.coprime_two_right.mp (mem_filter.mp hk).2).exists_bit1 with ⟨j,hj⟩
      refine ⟨j,?_,hj.symm⟩
      apply mem_range.mpr
      omega
    · intro j hj
      rfl
  rw [←heq]
  have hi := odd_progression_power_sum_upper M a ha ha1
  have hp : ((2*M+1 : ℕ) : ℝ)^a ≤ (N : ℝ)^a :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hMN) ha.le
  exact hi.trans (add_le_add (le_refl 1) (div_le_div_of_nonneg_right (sub_le_sub_right hp 1)
    (show (0 : ℝ) ≤ 2*a by positivity)))

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2600000
open Finset Nat Real
open scoped BigOperators Classical
namespace Helfgott

lemma max_floor_half_quotient (A D : ℕ) (hD : 1 ≤ D) :
    A ≤ 2*D*(max 1 (A/D)) := by
  have hi := Nat.lt_mul_div_succ A (by omega : 0 < D)
  have h1 := le_max_left (1 : ℕ) (A/D)
  have hq := le_max_right (1 : ℕ) (A/D)
  have hsum : (A/D : ℕ)+1 ≤ 2*max 1 (A/D) := by omega
  calc
    A ≤ D*((A/D : ℕ)+1) := Nat.le_of_lt hi
    _ ≤ D*(2*max 1 (A/D)) := Nat.mul_le_mul_left D hsum
    _ = _ := by ring

lemma floor_rankin_power_upper (U A k : ℕ) (L gamma : ℝ)
    (hA : 1 ≤ A) (hk : 1 ≤ k) (hL : 0 ≤ L) (hg : 0 ≤ gamma) :
    (L/(max 1 (A/((U+1)*k)) : ℕ))^gamma ≤
      (2*L*(U+1 : ℕ)/A)^gamma*(k : ℝ)^gamma := by
  let D : ℕ := (U+1)*k
  let N : ℕ := max 1 (A/D)
  have hD : 1 ≤ D := by
    dsimp only [D]
    simpa using Nat.mul_le_mul (show 1 ≤ U+1 by omega) hk
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hNr : (0 : ℝ) < N := by dsimp [N];exact_mod_cast (le_max_left 1 (A/D))
  have hfloor : (A : ℝ) ≤ 2*(D : ℝ)*N := by exact_mod_cast max_floor_half_quotient A D hD
  have hlo : (A : ℝ)/(2*D) ≤ N := (div_le_iff₀ (by positivity : (0 : ℝ)<2*D)).mpr (by nlinarith)
  have hquot := div_le_div_of_nonneg_left hL (div_pos hAr (by positivity : (0 : ℝ)<2*D)) hlo
  have hrat : L/((A : ℝ)/(2*D))=(2*L*(U+1 : ℕ)/A)*k := by
    dsimp only [D]
    push_cast
    field_simp
    <;> ring
  rw [hrat] at hquot
  have hp := Real.rpow_le_rpow (div_nonneg hL hNr.le) hquot hg
  apply hp.trans_eq
  exact Real.mul_rpow (by positivity) (Nat.cast_nonneg k)

theorem odd_floor_two_power_sum_upper_complete (U A Y : ℕ) (L T alpha beta : ℝ)
    (hA : 1 ≤ A) (hY : 1 ≤ Y) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (ha : 0 ≤ alpha) (hb : 0 ≤ beta) (hab0 : 0 < alpha+beta) (hab1 : alpha+beta ≤ 1) :
    (∑ k∈Icc 1 Y,if Nat.Coprime k 2 then
      (L/(max 1 (A/((U+1)*k)) : ℕ))^alpha*
        (T/(max 1 (A/((U+1)*k)) : ℕ))^beta/k else 0) ≤
      (2*L*(U+1 : ℕ)/A)^alpha*(2*T*(U+1 : ℕ)/A)^beta*
        (1+((Y : ℝ)^(alpha+beta)-1)/(2*(alpha+beta))) := by
  let C : ℝ := (2*L*(U+1 : ℕ)/A)^alpha*(2*T*(U+1 : ℕ)/A)^beta
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hi : (∑ k∈Icc 1 Y,if Nat.Coprime k 2 then
      (L/(max 1 (A/((U+1)*k)) : ℕ))^alpha*
        (T/(max 1 (A/((U+1)*k)) : ℕ))^beta/k else 0) ≤
      C*(∑ k∈Icc 1 Y,if Nat.Coprime k 2 then (k : ℝ)^(alpha+beta-1) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hkI
    by_cases hodd : Nat.Coprime k 2
    · rw [if_pos hodd,if_pos hodd]
      have hk := (mem_Icc.mp hkI).1
      have hkp : (0 : ℝ)<k := by exact_mod_cast hk
      have hp := floor_rankin_power_upper U A k L alpha hA hk hL ha
      have hz := floor_rankin_power_upper U A k T beta hA hk hT hb
      have hprod := mul_le_mul hp hz (by positivity) (by positivity)
      have hd := div_le_div_of_nonneg_right hprod (Nat.cast_nonneg k)
      apply hd.trans_eq
      rw [Real.rpow_sub hkp,Real.rpow_one,Real.rpow_add hkp]
      dsimp only [C]
      ring
    · simp only [if_neg hodd,mul_zero,le_refl]
  exact hi.trans (mul_le_mul_of_nonneg_left (odd_power_sum_upper Y (alpha+beta) hY hab0 hab1) hC)

end Helfgott
end

open Helfgott Finset Nat Real
open scoped BigOperators Classical
theorem solution  (U A Y : ℕ) (L T alpha beta : ℝ)
    (hA : 1 ≤ A) (hY : 1 ≤ Y) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (ha : 0 ≤ alpha) (hb : 0 ≤ beta) (hab0 : 0 < alpha+beta) (hab1 : alpha+beta ≤ 1) :
    (∑ k∈Icc 1 Y,if Nat.Coprime k 2 then
      (L/(max 1 (A/((U+1)*k)) : ℕ))^alpha*
        (T/(max 1 (A/((U+1)*k)) : ℕ))^beta/k else 0) ≤
      (2*L*(U+1 : ℕ)/A)^alpha*(2*T*(U+1 : ℕ)/A)^beta*
        (1+((Y : ℝ)^(alpha+beta)-1)/(2*(alpha+beta))) := Helfgott.odd_floor_two_power_sum_upper_complete U A Y L T alpha beta hA hY hL hT ha hb hab0 hab1
#print axioms solution
