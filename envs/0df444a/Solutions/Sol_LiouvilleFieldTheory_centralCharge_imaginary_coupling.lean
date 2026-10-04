-- Prove2me | solution 1 for LiouvilleFieldTheory.centralCharge_imaginary_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:44:09.288993+00:00
-- url     : https://prove2.me/submissions/9a4a3079-6368-4f86-87d5-063a045788e2

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics

set_option autoImplicit false

open Complex

open LiouvilleFieldTheory in
lemma cc072_formula (β : ℝ) (hβ : β ≠ 0) :
    centralCharge (-I * β) = ((1 - 6 * (β⁻¹ - β) ^ 2 : ℝ) : ℂ) := by
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hinv : (-I * (β : ℂ))⁻¹ = I * (β : ℂ)⁻¹ := by
    rw [mul_inv, inv_neg, Complex.inv_I, neg_neg]
  unfold centralCharge backgroundCharge
  rw [hinv]
  push_cast
  linear_combination (6 * ((β : ℂ)⁻¹ - (β : ℂ)) ^ 2) * Complex.I_sq

open Complex LiouvilleFieldTheory in
theorem solution :
    {c : ℂ | ∃ β : ℝ, β ≠ 0 ∧ centralCharge (-I * β) = c} =
      {c : ℂ | c.im = 0 ∧ c.re ≤ 1} := by
  ext c
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨β, hβ, rfl⟩
    rw [cc072_formula β hβ, Complex.ofReal_im, Complex.ofReal_re]
    refine ⟨rfl, ?_⟩
    nlinarith [sq_nonneg (β⁻¹ - β)]
  · rintro ⟨him, hre⟩
    set s : ℝ := Real.sqrt ((1 - c.re) / 6) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = (1 - c.re) / 6 := by
      rw [hs, Real.sq_sqrt]; linarith
    set t : ℝ := Real.sqrt (s ^ 2 + 4) with ht
    have ht2 : t ^ 2 = s ^ 2 + 4 := by
      rw [ht, Real.sq_sqrt]; positivity
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have hts : s < t := by nlinarith
    set β : ℝ := (t - s) / 2 with hβdef
    have hβpos : 0 < β := by rw [hβdef]; linarith
    have hβne : β ≠ 0 := ne_of_gt hβpos
    have hquad : β ^ 2 + s * β = 1 := by
      rw [hβdef]; nlinarith
    have hkey : β⁻¹ - β = s := by
      field_simp
      nlinarith
    refine ⟨β, hβne, ?_⟩
    rw [cc072_formula β hβne, hkey, hs2]
    apply Complex.ext
    · simp only [Complex.ofReal_re]; ring
    · simp only [Complex.ofReal_im]; exact him.symm
