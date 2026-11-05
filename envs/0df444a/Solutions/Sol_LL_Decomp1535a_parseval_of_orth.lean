-- Prove2me | solution 1 for LL_Decomp1535a.parseval_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:02.45029+00:00
-- url     : https://prove2.me/submissions/37924b21-d363-4fdb-a945-7fbab42e1988

import Mathlib
import Definitions.Def_LL_Decomp1535a_S

open MeasureTheory

theorem GbAAux.int_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i)) :
    ∫ α in (0 : ℝ)..1, ∑ i ∈ s, f i α = ∑ i ∈ s, ∫ α in (0 : ℝ)..1, f i α :=
  intervalIntegral.integral_finsetSum fun i _ => (hf i).intervalIntegrable _ _

theorem GbAAux.exp_mul_conj (α : ℝ) (p q : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * α * p) *
      (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * α * q)) =
    Complex.exp (2 * Real.pi * Complex.I * α * (((p : ℤ) - q : ℤ) : ℂ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem GbAAux.parseval_of_orth
    (horth : ∀ k : ℤ, ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0) (N : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖LL_Decomp1535a.S N α‖ ^ 2 =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have key : ∀ α : ℝ, (((‖LL_Decomp1535a.S N α‖ ^ 2 : ℝ)) : ℂ) =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, ∑ q ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ((Real.log p : ℂ) * (Real.log q : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * α * (((p : ℤ) - q : ℤ) : ℂ)) := by
    intro α
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    unfold LL_Decomp1535a.S
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, Complex.conj_ofReal, ← GbAAux.exp_mul_conj]
    ring
  simp_rw [key]
  rw [GbAAux.int_sum _ _ (fun p => by fun_prop), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [GbAAux.int_sum _ _ (fun q => by fun_prop)]
  simp_rw [intervalIntegral.integral_const_mul, horth]
  simp [sub_eq_zero, hp, sq]

theorem solution (horth : ∀ k : ℤ, ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0) (N : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖LL_Decomp1535a.S N α‖ ^ 2 =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 :=
  GbAAux.parseval_of_orth horth N
