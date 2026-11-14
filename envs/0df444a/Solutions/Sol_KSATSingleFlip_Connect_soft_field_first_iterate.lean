-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_first_iterate
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:11:37.078771+00:00
-- url     : https://prove2.me/submissions/b544999b-6b22-40f6-bc0a-19f655520adb

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

private theorem cp_zero : compoundPoisson 0 = Measure.dirac (0:ℝ) := by
  unfold compoundPoisson
  simp only [Measure.coe_zero, Pi.zero_apply, ENNReal.zero_ne_top, ↓reduceIte, ENNReal.toReal_zero, neg_zero, Real.exp_zero]
  have hc : ∀ j : ℕ, convPow (0 : Measure ℝ) j = if j = 0 then Measure.dirac 0 else 0 := by
    intro j
    cases j with
    | zero => simp [convPow]
    | succ j => simp [convPow]
  simp_rw [hc]
  ext s hs
  rw [Measure.sum_apply _ hs]
  rw [tsum_eq_single 0]
  · simp
  · intro i hi
    simp [hi]

theorem solution (γ : ℝ) :
    nuIter γ 1 = ENNReal.ofReal (Real.exp (-γ)) • Measure.dirac (0:ℝ) ∧
    (massM (nuIter γ 1)).toReal = Real.exp (-γ) ∧
    hPot (nuIter γ 1) = c0 * Real.exp (-γ) := by
  have hk : Kmeas 0 = Measure.dirac (0:ℝ) := by
    unfold Kmeas
    simp [cp_zero]
  have hp : hPot 0 = 0 := by simp [hPot,pairing]
  have heq : nuIter γ 1 = ENNReal.ofReal (Real.exp (-γ)) • Measure.dirac (0:ℝ) := by
    simp [nuIter,Rbeta,hp,hk]
  refine ⟨heq,?_,?_⟩
  · rw [heq]
    simp [massM, Real.exp_nonneg]
  · rw [heq]
    have hq : qOf 0 = 1/2 := by norm_num [qOf]
    have hs : Real.sqrt (1/2:ℝ) = Real.sqrt 2 / 2 := by
      have h1 : 0 ≤ Real.sqrt (1/2:ℝ) := Real.sqrt_nonneg _
      have h2 : 0 ≤ Real.sqrt (2:ℝ) := Real.sqrt_nonneg _
      have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 1/2 by norm_num)
      have h4 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
      nlinarith
    have hg : gW (qOf 0) = c0 := by
      rw [hq]
      simp only [gW,c0]
      have hh : (1:ℝ) - 1/2 = 1/2 := by norm_num
      rw [hh, hs]
      ring
    simp [hPot,pairing,hg, Real.exp_nonneg, mul_comm]
