-- Prove2me | solution 1 for MeanVarASD.AFSD.A_ge_B_at_deltaStar
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:10:12.561653+00:00
-- url     : https://prove2.me/submissions/1b4c05da-ae8e-401e-9273-3cde1170822a

import Mathlib
import Definitions.Def_MeanVarASD_AFSD_Defs
set_option autoImplicit false

open MeanVarASD.AFSD

theorem solution (μX μY σX σY γ : ℝ) (hσX : 0 ≤ σX) (hσY : 0 ≤ σY)
    (hσ : 0 < σX + σY) (hμ : μX < μY) (hγ : gammaStar (tStat μX μY σX σY) ≤ γ) :
    Bval γ (deltaStar μX μY σX σY) μX σX ≤ Aval γ (deltaStar μX μY σX σY) μY σY := by
  have hσ' : σY + σX ≠ 0 := by linarith
  set t := tStat μX μY σX σY with ht
  have ht' : t * (σY + σX) = μY - μX := by
    rw [ht]; unfold tStat; field_simp
  have hd1 : μX - deltaStar μX μY σX σY = -(σX * t) := by
    unfold deltaStar
    have : μX - (μX * σY + μY * σX) / (σY + σX) = (μX * (σY + σX) - (μX * σY + μY * σX)) / (σY + σX) := by
      field_simp
    rw [this]
    have : μX * (σY + σX) - (μX * σY + μY * σX) = -(σX * (μY - μX)) := by ring
    rw [this, ← ht']
    field_simp
  have hd2 : μY - deltaStar μX μY σX σY = σY * t := by
    unfold deltaStar
    have : μY - (μX * σY + μY * σX) / (σY + σX) = (μY * (σY + σX) - (μX * σY + μY * σX)) / (σY + σX) := by
      field_simp
    rw [this]
    have : μY * (σY + σX) - (μX * σY + μY * σX) = σY * (μY - μX) := by ring
    rw [this, ← ht']
    field_simp
  set s := Real.sqrt (t ^ 2 + 1) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = t ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hst : t < s := by
    by_contra h; push_neg at h
    nlinarith
  have hm : 0 < s - t := by linarith
  have key : (1 + 2 * t * (t + s)) * (s - t) ^ 2 = 1 := by nlinarith [hs2]
  have hpos : 0 < 1 + 2 * t * (t + s) := by
    by_contra h; push_neg at h
    nlinarith [sq_nonneg (s - t)]
  have hgam : gammaStar t = (s - t) ^ 2 := by
    unfold gammaStar
    rw [← hs]
    field_simp
    nlinarith [key]
  rw [hgam] at hγ
  have hB : Real.sqrt (σX ^ 2 + (μX - deltaStar μX μY σX σY) ^ 2) = σX * s := by
    rw [hd1]
    have : σX ^ 2 + (-(σX * t)) ^ 2 = σX ^ 2 * (t ^ 2 + 1) := by ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hσX]
  have hA : Real.sqrt (σY ^ 2 + (μY - deltaStar μX μY σX σY) ^ 2) = σY * s := by
    rw [hd2]
    have : σY ^ 2 + (σY * t) ^ 2 = σY ^ 2 * (t ^ 2 + 1) := by ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hσY]
  have hd2' : deltaStar μX μY σX σY - μY = -(σY * t) := by linarith [hd2]
  unfold Bval Aval
  rw [hB, hA, hd1, hd2, hd2']
  have hX : 2 * (s - t) * (γ * t - (1 - γ) * (s - t) / 2) = γ - (s - t) ^ 2 := by
    nlinarith [hs2]
  have hX0 : 0 ≤ γ * t - (1 - γ) * (s - t) / 2 := by
    by_contra h
    push_neg at h
    have h2 : 2 * (s - t) * (γ * t - (1 - γ) * (s - t) / 2) < 0 := by
      have := mul_pos (by linarith : (0:ℝ) < 2 * (s - t)) (neg_pos.2 h)
      linarith
    linarith
  nlinarith [mul_nonneg hσ.le hX0]
