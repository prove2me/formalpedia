-- Prove2me | solution 1 for MeanVarASD.AFSD.deltaStar_minimizes_h
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:12:26.276002+00:00
-- url     : https://prove2.me/submissions/c972bc51-4ee6-48c7-9e81-53fb99d3df2b

import Mathlib
import Definitions.Def_MeanVarASD_AFSD_Defs
set_option autoImplicit false

open MeanVarASD.AFSD

lemma uu_tan (z w : ℝ) :
    fAux w + (1 + w / Real.sqrt (1 + w ^ 2)) * (z - w) ≤ fAux z ∧
    (fAux w + (1 + w / Real.sqrt (1 + w ^ 2)) * (z - w) = fAux z → z = w) := by
  have ha0 : 0 < Real.sqrt (1 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hb0 : 0 < Real.sqrt (1 + w ^ 2) := Real.sqrt_pos.2 (by positivity)
  set a := Real.sqrt (1 + z ^ 2) with ha
  set b := Real.sqrt (1 + w ^ 2) with hb
  have ha2 : a ^ 2 = 1 + z ^ 2 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = 1 + w ^ 2 := Real.sq_sqrt (by positivity)
  have hab : (a * b) ^ 2 = (1 + z * w) ^ 2 + (z - w) ^ 2 := by
    rw [mul_pow, ha2, hb2]; ring
  have hge : 1 + z * w ≤ a * b := by
    by_contra h; push_neg at h
    have : 0 ≤ a * b := by positivity
    nlinarith [sq_nonneg (z - w)]
  have e : fAux w + (1 + w / b) * (z - w) = z + b + w * (z - w) / b := by
    unfold fAux; rw [← hb]; field_simp; ring
  have key : w * (z - w) / b ≤ a - b ↔ w * (z - w) ≤ (a - b) * b := div_le_iff₀ hb0
  constructor
  · rw [e]; unfold fAux; rw [← ha]
    have : w * (z - w) ≤ (a - b) * b := by nlinarith
    have := key.2 this
    linarith
  · intro h
    rw [e] at h; unfold fAux at h; rw [← ha] at h
    have h2 : w * (z - w) / b = a - b := by linarith
    have h3 : w * (z - w) = (a - b) * b := by
      field_simp at h2; linarith
    have h4 : 1 + z * w = a * b := by nlinarith
    have h5 : (z - w) ^ 2 = 0 := by nlinarith
    have := pow_eq_zero_iff (two_ne_zero) |>.1 h5
    linarith

theorem solution (μX μY σX σY : ℝ) (hσX : 0 < σX) (hσY : 0 < σY) :
    ∀ δ, hAux μX μY σX σY (deltaStar μX μY σX σY) ≤ hAux μX μY σX σY δ ∧
      (hAux μX μY σX σY δ = hAux μX μY σX σY (deltaStar μX μY σX σY) →
        δ = deltaStar μX μY σX σY) := by
  intro δ
  have hσ' : σY + σX ≠ 0 := by positivity
  set t := (μY - μX) / (σY + σX) with ht
  have ht' : t * (σY + σX) = μY - μX := by
    rw [ht]; field_simp
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
  set w := -t with hw
  set c := 1 + w / Real.sqrt (1 + w ^ 2) with hc
  have hzY0 : (deltaStar μX μY σX σY - μY) / σY = w := by
    have : deltaStar μX μY σX σY - μY = -(σY * t) := by linarith
    rw [this, hw]; field_simp
  have hzX0 : (μX - deltaStar μX μY σX σY) / σX = w := by
    rw [hd1, hw]; field_simp
  have hmin : hAux μX μY σX σY (deltaStar μX μY σX σY) = (σY + σX) * fAux w := by
    unfold hAux; rw [hzY0, hzX0]; ring
  obtain ⟨hY1, hY2⟩ := uu_tan ((δ - μY) / σY) w
  obtain ⟨hX1, hX2⟩ := uu_tan ((μX - δ) / σX) w
  -- linear combination
  have hlin : σY * (c * ((δ - μY) / σY - w)) + σX * (c * ((μX - δ) / σX - w)) = 0 := by
    have e1 : σY * ((δ - μY) / σY - w) = δ - μY - σY * w := by field_simp
    have e2 : σX * ((μX - δ) / σX - w) = μX - δ - σX * w := by field_simp
    have : σY * (c * ((δ - μY) / σY - w)) + σX * (c * ((μX - δ) / σX - w))
        = c * (σY * ((δ - μY) / σY - w) + σX * ((μX - δ) / σX - w)) := by ring
    rw [this, e1, e2]
    have : δ - μY - σY * w + (μX - δ - σX * w) = μX - μY - (σY + σX) * w := by ring
    rw [this, hw]
    have : μX - μY - (σY + σX) * -t = 0 := by nlinarith [ht']
    rw [this]; ring
  have hY1' := mul_le_mul_of_nonneg_left hY1 hσY.le
  have hX1' := mul_le_mul_of_nonneg_left hX1 hσX.le
  have hge : (σY + σX) * fAux w ≤ hAux μX μY σX σY δ := by
    unfold hAux
    nlinarith [hY1', hX1', hlin]
  refine ⟨by rw [hmin]; exact hge, ?_⟩
  intro heq
  rw [hmin] at heq
  have hsY : σY * (fAux w + c * ((δ - μY) / σY - w)) = σY * fAux ((δ - μY) / σY) := by
    have : fAux w + c * ((δ - μY) / σY - w) = fAux ((δ - μY) / σY) := by
      apply le_antisymm hY1
      by_contra hlt
      push_neg at hlt
      unfold hAux at heq
      nlinarith [mul_lt_mul_of_pos_left hlt hσY, hX1', hlin]
    rw [this]
  have hY := hY2 (mul_left_cancel₀ hσY.ne' hsY)
  have : δ - μY = σY * w := by
    rw [div_eq_iff hσY.ne'] at hY
    linarith
  have : δ = μY + σY * w := by linarith
  have hd2' : deltaStar μX μY σX σY = μY - σY * t := by linarith [hd2]
  rw [hd2', this, hw]; ring
