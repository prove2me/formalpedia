-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_threshold_scalar_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:08:46.280448+00:00
-- url     : https://prove2.me/submissions/ae1ac3dd-3f58-4f4b-9565-7917ac039a02

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_mass_potential_comparison
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_iterates_well_defined
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_threshold_partial
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

private theorem c0_pos : 0 < c0 := by
  have hr : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  unfold c0
  nlinarith

private theorem exp_tangent (h : ℝ) : h * Real.exp (1 : ℝ) ≤ Real.exp h := by
  have he := Real.add_one_le_exp (h-1)
  have he' : h ≤ Real.exp (h-1) := by linarith
  have hh1 := mul_le_mul_of_nonneg_right he' (le_of_lt (Real.exp_pos 1))
  rw [← Real.exp_add] at hh1
  convert hh1 using 1 <;> congr 1 <;> ring

private theorem factor_gt_one (γ : ℝ) (hγ : γ < 1+Real.log c0) :
    1 < Real.exp (1-γ)*c0 := by
  have he : 1 < Real.exp ((1-γ) + Real.log c0) := Real.one_lt_exp_iff.mpr (by linarith)
  rw [Real.exp_add, Real.exp_log c0_pos] at he
  exact he

private theorem grow_iter (γ : ℝ) (hγ : γ < 1+Real.log c0) :
    ∀ r : ℕ, Real.exp (-γ) + (r:ℝ)*((Real.exp (1-γ)*c0-1)*Real.exp (-γ)) ≤
      (massM (nuIter γ (r+1))).toReal := by
  have hk := factor_gt_one γ hγ
  have hd : 0 < (Real.exp (1-γ)*c0-1)*Real.exp (-γ) := mul_pos (by linarith) (Real.exp_pos _)
  intro r
  induction r with
  | zero =>
    have hrec := (soft_field_iterates_well_defined γ 0).2.2.2.1
    have hz : hPot (nuIter γ 0) = 0 := by simp [nuIter, hPot, pairing]
    rw [hz] at hrec
    simp only [Real.exp_zero, mul_one] at hrec
    simp only [Nat.cast_zero, zero_mul, add_zero]
    exact le_of_eq hrec.symm
  | succ r ih =>
    letI : IsFiniteMeasure (nuIter γ (r+1)) := (soft_field_iterates_well_defined γ (r+1)).1
    have hh := (soft_field_mass_potential_comparison (nuIter γ (r+1))).1
    have hrec := (soft_field_iterates_well_defined γ (r+1)).2.2.2.1
    let m := (massM (nuIter γ (r+1))).toReal
    let h := hPot (nuIter γ (r+1))
    have hmass : Real.exp (-γ) ≤ m := by
      dsimp [m]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) r) (le_of_lt hd)]
    have hh' : c0*m ≤ h := hh
    have ht := mul_le_mul_of_nonneg_left (exp_tangent h) (le_of_lt (Real.exp_pos (-γ)))
    have heq : Real.exp (1-γ) = Real.exp (-γ)*Real.exp 1 := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hlower : (Real.exp (1-γ)*c0)*m ≤ Real.exp (-γ)*Real.exp h := by
      rw [heq]
      nlinarith [mul_nonneg (sub_nonneg.mpr hh') (le_of_lt (Real.exp_pos (-γ))),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hh') (le_of_lt (Real.exp_pos (-γ)))) (le_of_lt (Real.exp_pos 1))]
    have hdiff : (Real.exp (1-γ)*c0-1)*Real.exp (-γ) ≤
        (Real.exp (1-γ)*c0-1)*m := mul_le_mul_of_nonneg_left hmass (by linarith)
    have hi : nuIter γ (r+1+1) = nuIter γ (r.succ+1) := by congr 2
    rw [hi] at hrec
    rw [hrec]
    push_cast
    dsimp [m] at *
    nlinarith

theorem solution :
    (∀ γ : ℝ, γ < 1+Real.log c0 → (⨆ r : ℕ, mIter γ r) = ∞) ∧
    1+Real.log c0 ≤ gammaStar := by
  have hg : ∀ γ : ℝ, γ < 1+Real.log c0 → (⨆ r : ℕ, mIter γ r) = ∞ := by
    intro γ hγ
    by_contra hh
    have hf : (⨆ r : ℕ, mIter γ r) ≠ ∞ := hh
    have hd : 0 < (Real.exp (1-γ)*c0-1)*Real.exp (-γ) :=
      mul_pos (by have hk := factor_gt_one γ hγ; linarith) (Real.exp_pos _)
    obtain ⟨r,hr⟩ := exists_nat_gt (((⨆ r : ℕ, mIter γ r).toReal) / ((Real.exp (1-γ)*c0-1)*Real.exp (-γ)))
    have hr' := (div_lt_iff₀ hd).mp hr
    have hlo := grow_iter γ hγ r
    have hhi : (massM (nuIter γ (r+1))).toReal ≤ ((⨆ r : ℕ, mIter γ r).toReal) :=
      ENNReal.toReal_mono hf (le_iSup (mIter γ) (r+1))
    have hp := Real.exp_pos (-γ)
    nlinarith
  refine ⟨hg,?_⟩
  unfold gammaStar
  apply le_csInf
  · exact ⟨1, soft_field_threshold_partial.1 1 le_rfl⟩
  · intro γ hγ
    by_contra hn
    have hsmall : γ < 1+Real.log c0 := lt_of_not_ge hn
    have he := hg γ hsmall
    change (⨆ r : ℕ, mIter γ r) < ∞ at hγ
    rw [he] at hγ
    exact lt_irrefl _ hγ
