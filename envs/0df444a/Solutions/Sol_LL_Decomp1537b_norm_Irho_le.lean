-- Prove2me | solution 1 for LL_Decomp1537b.norm_Irho_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:19.824029+00:00
-- url     : https://prove2.me/submissions/018fb9f5-236a-4dac-960c-27cbc1a39817

import Mathlib
import Definitions.Def_LL_Decomp1537b_I1
import Definitions.Def_LL_Decomp1537b_Irho

open Finset Real

theorem solution (N N1 : ℕ) (h : ℤ) {ρ ρ' : ℂ} (hρ : ρ.re ≤ 1) (hρ' : ρ'.re ≤ 1) :
    ‖LL_Decomp1537b.Irho N N1 h ρ ρ'‖ ≤ LL_Decomp1537b.I1 N N1 h := by
  unfold LL_Decomp1537b.Irho LL_Decomp1537b.I1
  refine (norm_sum_le _ _).trans ?_
  rw [card_eq_sum_ones, Nat.cast_sum]
  apply sum_le_sum
  intro m hm
  simp only [mem_filter, mem_Ioo] at hm
  obtain ⟨⟨hm1, hm2⟩, hm3, hm4⟩ := hm
  rw [norm_mul]
  have e1 : ‖(m : ℂ) ^ (ρ - 1)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (by omega : 1 ≤ m)
    · simp; linarith
  have e2 : ‖(((m : ℤ) - h : ℤ) : ℂ) ^ (ρ' - 1)‖ ≤ 1 := by
    have : (((m : ℤ) - h : ℤ) : ℂ) = (((((m : ℤ) - h : ℤ)) : ℝ) : ℂ) := by simp
    rw [this, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (by omega : (0:ℤ) < (m:ℤ) - h))]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (by omega : (1:ℤ) ≤ (m:ℤ) - h)
    · simp; linarith
  calc _ ≤ 1 * 1 := mul_le_mul e1 e2 (norm_nonneg _) zero_le_one
    _ ≤ ((1 : ℕ) : ℝ) := by norm_num
