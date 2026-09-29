-- Prove2me | solution 1 for LawsonCriterion.self_heating_substituted
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:35:30.005585+00:00
-- url     : https://prove2.me/submissions/2ad098c7-3e49-43b4-9e56-fd46077b511d

import Definitions.Def_LawsonDTPlasma

open LawsonCriterion

theorem L_power_loss_eq (p : DTPlasma) : p.Ploss = 3 * p.n * p.T / p.tauE := by
  have h := p.tauE_eq
  unfold energyDensity at h
  have h1 := p.Ploss_pos
  have h2 : 0 < 3 * p.n * p.T := by have := p.n_pos; have := p.T_pos; positivity
  have h3 : p.n * p.T ≠ 0 := by have := p.n_pos; have := p.T_pos; positivity
  rw [h]
  field_simp
  rw [div_self h3]

theorem L_fusion_rate_fifty_fifty (n sigmav : ℝ) :
    fusionRate (n / 2) (n / 2) sigmav = (1 / 4) * n ^ 2 * sigmav := by
  unfold fusionRate; ring

theorem L_self_heating_substituted (p : DTPlasma) (h : p.SelfHeating) :
    (1 / 4) * p.n ^ 2 * p.sigmav * p.Ech ≥ 3 * p.n * p.T / p.tauE := by
  have h' := h
  unfold DTPlasma.SelfHeating DTPlasma.fusionHeating DTPlasma.rate fusionRate at h'
  rw [← L_power_loss_eq]
  have e : (1 / 4) * p.n ^ 2 * p.sigmav * p.Ech = p.n / 2 * (p.n / 2) * p.sigmav * p.Ech := by ring
  rw [e]; exact h'

theorem L_lawson_criterion (p : DTPlasma) (h : p.SelfHeating) :
    p.n * p.tauE ≥ 12 * p.T / (p.Ech * p.sigmav) := by
  have h2 := L_self_heating_substituted p h
  have hn := p.n_pos; have hT := p.T_pos; have hs := p.sigmav_pos; have hE := p.Ech_pos
  have ht := p.tauE_pos
  have h3 : 3 * p.n * p.T ≤ (1 / 4) * p.n ^ 2 * p.sigmav * p.Ech * p.tauE := by
    rw [ge_iff_le, div_le_iff₀ ht] at h2; linarith
  rw [ge_iff_le, div_le_iff₀ (by positivity)]
  have h4 : p.n * (12 * p.T) ≤ p.n * (p.n * p.tauE * (p.Ech * p.sigmav)) := by nlinarith
  exact le_of_mul_le_mul_left h4 hn

theorem L_triple_product (p : DTPlasma) (h : p.SelfHeating) :
    p.n * p.T * p.tauE ≥ (12 / p.Ech) * (p.T ^ 2 / p.sigmav) := by
  have h1 := L_lawson_criterion p h
  have hT := p.T_pos; have hs := p.sigmav_pos; have hE := p.Ech_pos
  have e1 : (12 / p.Ech) * (p.T ^ 2 / p.sigmav) = p.T * (12 * p.T / (p.Ech * p.sigmav)) := by
    field_simp
  have e2 : p.n * p.T * p.tauE = p.T * (p.n * p.tauE) := by ring
  rw [e1, e2, ge_iff_le]
  exact mul_le_mul_of_nonneg_left h1 hT.le

theorem L_triple_product_DT_bound (p : DTPlasma) (h : p.SelfHeating)
    (hEch : p.Ech = 3500) (hsv : p.sigmav = (11 / 10 ^ 25) * p.T ^ 2) :
    p.n * p.T * p.tauE ≥ 3 * 10 ^ 21 := by
  have h1 := L_triple_product p h
  have hT := p.T_pos
  have e : (12 / p.Ech) * (p.T ^ 2 / p.sigmav) = 12 / 3500 * (10 ^ 25 / 11) := by
    rw [hEch, hsv]; field_simp
  rw [e] at h1
  linarith [show (3 : ℝ) * 10 ^ 21 ≤ 12 / 3500 * (10 ^ 25 / 11) by norm_num]

theorem L_tokamak_triple_product_scaling (c a n T P tauE : ℝ)
    (hn : 0 < n) (hT : 0 < T) (ha : 0 < a)
    (hP : P = a * n ^ 2 * T ^ 2)
    (htau : tauE = c * n ^ ((1:ℝ) / 3) / P ^ ((2:ℝ) / 3)) :
    n * T * tauE = c * a ^ (-(2/3) : ℝ) * T ^ (-(1/3) : ℝ) := by
  have hP23 : P ^ ((2:ℝ) / 3) = a ^ ((2:ℝ) / 3) * (n * n ^ ((1:ℝ) / 3)) * (T * T ^ ((1:ℝ) / 3)) := by
    rw [hP, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
    have hn2 : (n ^ 2) ^ ((2:ℝ) / 3) = n * n ^ ((1:ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_one_add' hn.le (by norm_num)]
      norm_num
    have hT2 : (T ^ 2) ^ ((2:ℝ) / 3) = T * T ^ ((1:ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le, ← Real.rpow_one_add' hT.le (by norm_num)]
      norm_num
    rw [hn2, hT2]
  rw [htau, hP23, Real.rpow_neg ha.le, Real.rpow_neg hT.le]
  have h1 : 0 < a ^ ((2:ℝ) / 3) := by positivity
  have h2 : 0 < n ^ ((1:ℝ) / 3) := by positivity
  have h3 : 0 < T ^ ((1:ℝ) / 3) := by positivity
  have e : (2 / 3 : ℝ) = (2:ℝ) / 3 := rfl
  have e' : (1 / 3 : ℝ) = (1:ℝ) / 3 := rfl
  field_simp

theorem solution (p : DTPlasma) (h : p.SelfHeating) :
    (1 / 4) * p.n ^ 2 * p.sigmav * p.Ech ≥ 3 * p.n * p.T / p.tauE := by
  apply L_self_heating_substituted <;> assumption
