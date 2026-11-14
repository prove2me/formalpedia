-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_threshold_lower_half
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:05:50.815273+00:00
-- url     : https://prove2.me/submissions/f3560f52-6992-4a8f-beba-f310a6ebb4b7

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_mass_potential_comparison
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_iterates_well_defined
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_threshold_partial
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

private theorem growth (m h γ : ℝ) (hm : 1/2 ≤ m) (hh : c0*m ≤ h) (hγ : γ ≤ 1/2) :
    m + 1/10 ≤ Real.exp (-γ)*Real.exp h := by
  have hr : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : (4/5:ℝ) ≤ c0 := by unfold c0; nlinarith
  have hhh : (4/5:ℝ)*m ≤ h := by nlinarith [mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ m by linarith)]
  have hp : 0 ≤ h := by linarith
  have hexp : h * Real.exp (1 : ℝ) ≤ Real.exp h := by
    have he := Real.add_one_le_exp (h-1)
    have he' : h ≤ Real.exp (h-1) := by linarith
    have hh1 := mul_le_mul_of_nonneg_right he' (le_of_lt (Real.exp_pos 1))
    rw [← Real.exp_add] at hh1
    convert hh1 using 1 <;> congr 1 <;> ring
  have hfactor : (3/2:ℝ) ≤ Real.exp (1-γ) := by
    have hh1 := Real.add_one_le_exp (1-γ)
    linarith
  have hcombine : h * Real.exp (1-γ) ≤ Real.exp (-γ)*Real.exp h := by
    have ht := mul_le_mul_of_nonneg_left hexp (le_of_lt (Real.exp_pos (-γ)))
    have heq : Real.exp (1-γ) = Real.exp (-γ)*Real.exp 1 := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    nlinarith
  have hhprod : (3/2:ℝ)*h ≤ h * Real.exp (1-γ) := by nlinarith [mul_nonneg (sub_nonneg.mpr hfactor) hp]
  nlinarith

private theorem grow_iter (γ : ℝ) (hγ : γ ≤ 1/2) :
    ∀ r : ℕ, (1/2:ℝ)+(r:ℝ)/10 ≤ (massM (nuIter γ (r+1))).toReal := by
  intro r
  induction r with
  | zero =>
    have hrec := (soft_field_iterates_well_defined γ 0).2.2.2.1
    have hz : hPot (nuIter γ 0) = 0 := by simp [nuIter, hPot, pairing]
    rw [hz] at hrec
    simp only [Real.exp_zero, mul_one] at hrec
    have hh := Real.add_one_le_exp (-γ)
    simp only [Nat.cast_zero, zero_div, add_zero]
    rw [hrec]
    linarith
  | succ r ih =>
    letI : IsFiniteMeasure (nuIter γ (r+1)) := (soft_field_iterates_well_defined γ (r+1)).1
    have hh := (soft_field_mass_potential_comparison (nuIter γ (r+1))).1
    have hrec := (soft_field_iterates_well_defined γ (r+1)).2.2.2.1
    have hmass : 1/2 ≤ (massM (nuIter γ (r+1))).toReal := by nlinarith [Nat.cast_nonneg (α := ℝ) r]
    have ht := growth (massM (nuIter γ (r+1))).toReal (hPot (nuIter γ (r+1))) γ hmass hh hγ
    have hi : nuIter γ (r+1+1) = nuIter γ (r.succ+1) := by congr 2 <;> omega
    rw [hi] at hrec
    rw [hrec]
    push_cast
    linarith

theorem solution :
    (∀ γ : ℝ, γ ≤ 1/2 → (⨆ r : ℕ, mIter γ r) = ∞) ∧
    (1/2 : ℝ) ≤ gammaStar := by
  have hg : ∀ γ : ℝ, γ ≤ 1/2 → (⨆ r : ℕ, mIter γ r) = ∞ := by
    intro γ hγ
    by_contra hh
    have hf : (⨆ r : ℕ, mIter γ r) ≠ ∞ := hh
    obtain ⟨r,hr⟩ := exists_nat_gt (10*((⨆ r : ℕ, mIter γ r).toReal))
    have hlo := grow_iter γ hγ r
    have hhi : (massM (nuIter γ (r+1))).toReal ≤ ((⨆ r : ℕ, mIter γ r).toReal) :=
      ENNReal.toReal_mono hf (le_iSup (mIter γ) (r+1))
    linarith
  refine ⟨hg,?_⟩
  unfold gammaStar
  apply le_csInf
  · exact ⟨1, soft_field_threshold_partial.1 1 le_rfl⟩
  · intro γ hγ
    by_contra hn
    have hsmall : γ ≤ 1/2 := le_of_lt (lt_of_not_ge hn)
    have he := hg γ hsmall
    change (⨆ r : ℕ, mIter γ r) < ∞ at hγ
    rw [he] at hγ
    exact lt_irrefl _ hγ
