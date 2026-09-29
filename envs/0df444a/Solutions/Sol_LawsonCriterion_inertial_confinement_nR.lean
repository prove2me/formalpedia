-- Prove2me | solution 1 for LawsonCriterion.inertial_confinement_nR
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T20:55:23.836008+00:00
-- url     : https://prove2.me/submissions/8da8e9bd-a248-4e55-983a-3dc07f0075c2

import Mathlib
import Definitions.Def_LawsonDTPlasma

open LawsonCriterion in
theorem solution (p : LawsonCriterion.DTPlasma) (R mi : ℝ) (hmi : 0 < mi)
    (htau : p.tauE = R * Real.sqrt (mi / p.T)) (h : p.SelfHeating) :
    p.n * R ≥ 12 * p.T ^ ((3:ℝ) / 2) / (p.Ech * p.sigmav * Real.sqrt mi) := by
  have hn := p.n_pos
  have hT := p.T_pos
  have hsv := p.sigmav_pos
  have hE := p.Ech_pos
  have htp := p.tauE_pos
  have hP := p.Ploss_pos
  have hs : 0 < Real.sqrt p.T := Real.sqrt_pos.mpr hT
  have hm : 0 < Real.sqrt mi := Real.sqrt_pos.mpr hmi
  have hss : Real.sqrt p.T * Real.sqrt p.T = p.T := Real.mul_self_sqrt hT.le
  have hpow : p.T ^ ((3:ℝ) / 2) = p.T * Real.sqrt p.T := by
    rw [Real.sqrt_eq_rpow, show (3:ℝ) / 2 = 1 + 1 / 2 by norm_num,
      Real.rpow_add hT, Real.rpow_one]
  have hdiv : Real.sqrt (mi / p.T) = Real.sqrt mi / Real.sqrt p.T :=
    Real.sqrt_div hmi.le p.T
  have htauS : p.tauE * Real.sqrt p.T = R * Real.sqrt mi := by
    rw [htau, hdiv]; field_simp
  have hPl : p.Ploss * p.tauE = 3 * p.n * p.T := by
    have := p.tauE_eq
    unfold energyDensity at this
    rw [this]; field_simp
  have hH : p.n / 2 * (p.n / 2) * p.sigmav * p.Ech ≥ p.Ploss := by
    have := h
    unfold DTPlasma.SelfHeating DTPlasma.fusionHeating DTPlasma.rate fusionRate at this
    exact this
  -- n τE σv Ech ≥ 12 T
  have key1 : p.n / 2 * (p.n / 2) * p.sigmav * p.Ech * p.tauE ≥ 3 * p.n * p.T := by
    rw [← hPl]; exact mul_le_mul_of_nonneg_right hH htp.le
  have key2 : p.n * p.sigmav * p.Ech * p.tauE ≥ 12 * p.T := by
    have e : p.n / 2 * (p.n / 2) * p.sigmav * p.Ech * p.tauE
        = p.n * (p.n * p.sigmav * p.Ech * p.tauE) / 4 := by ring
    rw [e] at key1
    have : p.n * (12 * p.T) ≤ p.n * (p.n * p.sigmav * p.Ech * p.tauE) := by linarith
    exact le_of_mul_le_mul_left this hn
  have key3 : p.n * p.sigmav * p.Ech * p.tauE * Real.sqrt p.T ≥ 12 * p.T * Real.sqrt p.T :=
    mul_le_mul_of_nonneg_right key2 hs.le
  have key4 : 12 * (p.T * Real.sqrt p.T) ≤ p.n * R * (p.Ech * p.sigmav * Real.sqrt mi) := by
    have e : p.n * p.sigmav * p.Ech * p.tauE * Real.sqrt p.T
        = p.n * p.sigmav * p.Ech * (p.tauE * Real.sqrt p.T) := by ring
    rw [e, htauS] at key3
    linarith
  rw [hpow, ge_iff_le, div_le_iff₀ (by positivity)]
  exact key4
