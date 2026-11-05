-- Prove2me | solution 1 for LL_Decomp1535a.circle_identity_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:03.612456+00:00
-- url     : https://prove2.me/submissions/296ea1a0-623c-4527-a1ad-3e6b7b0dfb26

import Mathlib
import Definitions.Def_LL_Decomp1535a_R3
import Definitions.Def_LL_Decomp1535a_S
import Definitions.Def_LL_Decomp1535a_F

open MeasureTheory

noncomputable def GbAAux.R3A (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N + 1),
    if p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = N then
      Real.log p * Real.log q * Real.log r else 0

theorem GbAAux.int_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i)) :
    ∫ α in (0 : ℝ)..1, ∑ i ∈ s, f i α = ∑ i ∈ s, ∫ α in (0 : ℝ)..1, f i α :=
  intervalIntegral.integral_finsetSum fun i _ => (hf i).intervalIntegrable _ _

theorem GbAAux.circle_identity_of_orth
    (horth : ∀ k : ℤ, ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0) (N : ℕ) :
    (GbAAux.R3A N : ℂ) = ∫ α in (0 : ℝ)..1, LL_Decomp1535a.F N α := by
  have key : ∀ α : ℝ, LL_Decomp1535a.F N α =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, ∑ q ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ∑ r ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ((Real.log p : ℂ) * (Real.log q : ℂ) * (Real.log r : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * α * (((p : ℤ) + q + r - N : ℤ) : ℂ)) := by
    intro α
    unfold LL_Decomp1535a.F LL_Decomp1535a.S
    simp only [pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun r _ => ?_
    have e : Complex.exp (2 * Real.pi * Complex.I * α * (((p : ℤ) + q + r - N : ℤ) : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I * α * p) * Complex.exp (2 * Real.pi * Complex.I * α * q) *
          Complex.exp (2 * Real.pi * Complex.I * α * r) *
          Complex.exp (-(2 * Real.pi * Complex.I * α * N)) := by
      simp only [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e]
    ring
  simp_rw [key]
  rw [GbAAux.int_sum _ _ (fun p => by fun_prop)]
  have step : ∀ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      ∫ α in (0 : ℝ)..1, ∑ q ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ∑ r ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ((Real.log p : ℂ) * (Real.log q : ℂ) * (Real.log r : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * α * (((p : ℤ) + q + r - N : ℤ) : ℂ)) =
      ∑ q ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ∑ r ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ((Real.log p : ℂ) * (Real.log q : ℂ) * (Real.log r : ℂ)) *
          (if ((p : ℤ) + q + r - N) = 0 then 1 else 0) := by
    intro p _
    rw [GbAAux.int_sum _ _ (fun q => by fun_prop)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [GbAAux.int_sum _ _ (fun r => by fun_prop)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [intervalIntegral.integral_const_mul, horth]
  rw [Finset.sum_congr rfl step]
  unfold GbAAux.R3A
  simp only [Finset.sum_filter, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p.Prime
  · simp only [hp, if_true]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q.Prime
    · simp only [hq, if_true]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : r.Prime
      · have : ((p : ℤ) + q + r - N = 0) ↔ p + q + r = N := by omega
        simp only [hr, true_and, if_true, this]
        split_ifs <;> simp
      · simp [hr]
    · simp [hq]
  · simp [hp]

theorem solution (horth : ∀ k : ℤ, ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0) (N : ℕ) :
    (LL_Decomp1535a.R3 N : ℂ) = ∫ α in (0 : ℝ)..1, LL_Decomp1535a.F N α :=
  GbAAux.circle_identity_of_orth horth N
