-- Prove2me | solution 1 for Helfgott.odd_harmonic_sum_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T05:45:52.035787+00:00
-- url     : https://prove2.me/submissions/74daa3be-d6c0-4530-b665-80310c0a9c3c

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

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
set_option maxHeartbeats 2000000
open Finset Nat Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott
lemma harmonicUpload_odd_sum_reindex (N : ℕ) (hN : 1 ≤ N) (f : ℕ → ℝ) :
    (∑ j∈range ((N-1)/2+1),f (2*j+1)) =
      ∑ k∈Icc 1 N,if Nat.Coprime k 2 then f k else 0 := by
  let M : ℕ := (N-1)/2
  have hMN : 2*M+1 ≤ N := by dsimp only [M];omega
  have hNM : N ≤ 2*M+2 := by dsimp only [M];omega
  have heq : (∑ j∈range (M+1),f (2*j+1))=
      ∑ k∈Icc 1 N,if Nat.Coprime k 2 then f k else 0 := by
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

  exact heq

lemma harmonicUpload_odd_harmonic_step (M : ℕ) :
    1/((2*(M+1)+1 : ℕ) : ℝ) ≤
      (Real.log ((2*(M+1)+1 : ℕ) : ℝ)-Real.log ((2*M+1 : ℕ) : ℝ))/2 := by
  let l : ℝ := (2*M+1 : ℕ)
  let r : ℝ := (2*(M+1)+1 : ℕ)
  have hl : 0 < l := by dsimp [l];positivity
  have hlr : l ≤ r := by dsimp [l,r];push_cast;nlinarith
  have hr : 0 < r := lt_of_lt_of_le hl hlr
  have hno : (0 : ℝ) ∉ Set.uIcc l r := by
    rw [Set.uIcc_of_le hlr]
    simp only [Set.mem_Icc,not_and]
    intro hh
    exact False.elim ((not_le_of_gt hl) hh)
  have hint : IntervalIntegrable (fun x : ℝ => x⁻¹) volume l r :=
    (continuousOn_inv₀.mono (by intro x hx;exact ne_of_mem_of_not_mem hx hno)).intervalIntegrable
  have hi := intervalIntegral.integral_mono_on hlr
    (intervalIntegrable_const (c := r⁻¹)) hint
    (fun x hx => inv_le_inv₀ hr (lt_of_lt_of_le hl hx.1) |>.mpr hx.2)
  rw [integral_inv_of_pos hl hr,Real.log_div hr.ne' hl.ne',intervalIntegral.integral_const] at hi
  have hlen : r-l=2 := by dsimp [l,r];push_cast;ring
  rw [hlen] at hi
  simp only [smul_eq_mul] at hi
  change 1/r ≤ (Real.log r-Real.log l)/2
  rw [one_div]
  linarith

theorem harmonicUpload_odd_harmonic_progression_upper (M : ℕ) :
    (∑ j∈range (M+1),1/((2*j+1 : ℕ) : ℝ)) ≤
      1+Real.log ((2*M+1 : ℕ) : ℝ)/2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hi := add_le_add ih (harmonicUpload_odd_harmonic_step M)
    apply hi.trans_eq
    push_cast
    ring

theorem odd_harmonic_sum_upper_complete (N : ℕ) (hN : 1 ≤ N) :
    (∑ k∈Icc 1 N,if Nat.Coprime k 2 then 1/(k : ℝ) else 0) ≤
      1+Real.log (N : ℝ)/2 := by
  rw [←harmonicUpload_odd_sum_reindex N hN (fun k => 1/(k : ℝ))]
  have hi := harmonicUpload_odd_harmonic_progression_upper ((N-1)/2)
  have hMN : 2*((N-1)/2)+1 ≤ N := by omega
  have hl : Real.log ((2*((N-1)/2)+1 : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hMN)
  exact hi.trans (add_le_add (le_refl 1) (div_le_div_of_nonneg_right hl (by norm_num : (0 : ℝ) ≤ 2)))
end Helfgott
end

open Helfgott Finset Nat Real ArithmeticFunction MeasureTheory
open scoped BigOperators Classical Interval
theorem solution  (N : ℕ) (hN : 1 ≤ N) :
    (∑ k∈Icc 1 N,if Nat.Coprime k 2 then 1/(k : ℝ) else 0) ≤
      1+Real.log (N : ℝ)/2 := Helfgott.odd_harmonic_sum_upper_complete N hN
#print axioms solution
