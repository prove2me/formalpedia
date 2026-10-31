-- Prove2me | solution 1 for MinBuying.canonical_boundary_replacement
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:41:24.701052+00:00
-- url     : https://prove2.me/submissions/fd6d13d2-6428-452e-93b9-fdb9752a134b

import Definitions.Def_MinBuying_Triangular

open MinBuying

theorem solution (a p C : ℝ)
    (ha : 0 < a) (hp : 1 < p) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hcross : 1 < continuationStep a p C)
    (hUP : p * (1 - (p / (p + C)) * (p / (p + a))) ≤ 1) :
    let D := continuationStep a p C
    let b := p * (D - 1) / (p - D)
    0 < b ∧ D < p ∧ D ≤ 1 + C ∧ continuationStep b p 1 = D ∧
      (∀ t : ℝ, 0 ≤ t → (t + 1) * (t + b) ≤ (t + C) * (t + a)) ∧
      (∀ ε z : ℝ, 0 ≤ ε → 1 - ε ≤ z → D - ε ≤ continuationStep b p z) := by
  let D := continuationStep a p C
  let b := p * (D - 1) / (p - D)
  change 0 < b ∧ D < p ∧ D ≤ 1 + C ∧ continuationStep b p 1 = D ∧
    (∀ t : ℝ, 0 ≤ t → (t + 1) * (t + b) ≤ (t + C) * (t + a)) ∧
    (∀ ε z : ℝ, 0 ≤ ε → 1 - ε ≤ z → D - ε ≤ continuationStep b p z)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpa : 0 < p + a := add_pos hp0 ha
  have hpC : 0 < p + C := add_pos_of_pos_of_nonneg hp0 hC0
  have hD1 : 1 < D := hcross
  have hDexpr : D = p * (a + C) / (p + a) := by
    dsimp [D, continuationStep]
    field_simp <;> ring
  have hDp : D < p := by
    rw [hDexpr]
    apply (div_lt_iff₀ hpa).2
    nlinarith only [mul_lt_mul_of_pos_left (lt_of_le_of_lt hC1 hp) hp0]
  have hpD : 0 < p - D := sub_pos.mpr hDp
  have hDeq : D * (p + a) = p * (a + C) := (eq_div_iff hpa.ne').mp hDexpr
  have haexpr : a = p * (D - C) / (p - D) := by
    apply (eq_div_iff hpD.ne').2
    nlinarith only [hDeq]
  have hpaexpr : p + a = p * (p - C) / (p - D) := by
    rw [haexpr]
    field_simp <;> ring
  have hUform : p * (1 - (p / (p + C)) * (p / (p + a))) =
      p - p ^ 3 / ((p + C) * (p + a)) := by
    field_simp <;> ring
  rw [hUform] at hUP
  have hUdiv : p - 1 ≤ p ^ 3 / ((p + C) * (p + a)) := by linarith
  have hUprod := (le_div_iff₀ (mul_pos hpC hpa)).mp hUdiv
  rw [hpaexpr] at hUprod
  have hUratio : ((p - 1) * (p + C) * (p * (p - C))) / (p - D) ≤ p ^ 3 := by
    simpa [mul_div_assoc, mul_assoc] using hUprod
  have hUcleared := (div_le_iff₀ hpD).mp hUratio
  have hUweighted : p * (p ^ 2 * (D - 1)) ≤ p * ((p - 1) * C ^ 2) := by
    nlinarith only [hUcleared]
  have hDsquare : p ^ 2 * (D - 1) ≤ (p - 1) * C ^ 2 :=
    (mul_le_mul_iff_right₀ hp0).mp hUweighted
  have hC2 : C ^ 2 ≤ C := by nlinarith only [mul_nonneg hC0 (sub_nonneg.mpr hC1)]
  have hpp : p - 1 ≤ p ^ 2 := by nlinarith only [sq_nonneg (p - 1 / 2)]
  have hDweak : D ≤ 1 + C := by
    have hbnd : (p - 1) * C ^ 2 ≤ p ^ 2 * C :=
      (mul_le_mul_of_nonneg_left hC2 (sub_nonneg.mpr hp.le)).trans
        (mul_le_mul_of_nonneg_right hpp hC0)
    have hle : D - 1 ≤ C :=
      (mul_le_mul_iff_right₀ (sq_pos_of_pos hp0)).mp (hDsquare.trans hbnd)
    linarith
  have hb : 0 < b := div_pos (mul_pos hp0 (sub_pos.mpr hD1)) hpD
  have hbrel : b * (p - D) = p * (D - 1) := by
    dsimp [b]
    exact div_mul_cancel₀ _ hpD.ne'
  have hden : 0 < 1 + b / p := by positivity
  have hstep : continuationStep b p 1 = D := by
    unfold continuationStep
    apply (div_eq_iff hden.ne').2
    have heq : (b + 1) * p = D * (p + b) := by nlinarith only [hbrel]
    field_simp
    nlinarith only [heq]
  refine ⟨hb, hDp, hDweak, hstep, ?_, ?_⟩
  · intro t ht
    have hid : (t + C) * (t + a) - (t + 1) * (t + b) =
        (1 - C) / (p - D) * (D * t + p * (1 + C - D)) := by
      rw [haexpr]
      dsimp [b]
      field_simp
      ring
    have hnn : 0 ≤ (1 - C) / (p - D) * (D * t + p * (1 + C - D)) := by
      apply mul_nonneg (div_nonneg (sub_nonneg.mpr hC1) hpD.le)
      exact add_nonneg (mul_nonneg (le_of_lt (lt_trans zero_lt_one hD1)) ht)
        (mul_nonneg hp0.le (sub_nonneg.mpr hDweak))
    linarith only [hid, hnn]
  · intro ε z hε hz
    have hden1 : 1 ≤ 1 + b / p := by have := div_nonneg hb.le hp0.le; linarith
    have hDden : D * (1 + b / p) = b + 1 :=
      (eq_div_iff hden.ne').mp hstep.symm
    unfold continuationStep
    apply (le_div_iff₀ hden).2
    nlinarith only [hDden, hz, mul_le_mul_of_nonneg_left hden1 hε]
