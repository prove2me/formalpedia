-- Prove2me | solution 1 for MassEnergyEquivalence.invariant_under_boost
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:52:02.852441+00:00
-- url     : https://prove2.me/submissions/6c315a72-a558-48a5-ba57-e3ba35e46e9c

import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_MassEnergyEquivalence_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MassEnergyEquivalence Filter Asymptotics Topology

/-- Longitudinal Lorentz boosts preserve the energy-momentum quadratic form. -/
theorem solution (c u E : ℝ) (p : Vec3) (hc : 0 < c) (hu : |u| < c) :
    boostEnergy c u E p ^ 2 - c ^ 2 * ‖boostMomentum c u E p‖ ^ 2 =
      E ^ 2 - c ^ 2 * ‖p‖ ^ 2 := by
  have hcn : 0 < c ^ 2 := sq_pos_of_pos hc
  have ha : 0 < c - |u| := sub_pos.mpr hu
  have hb : 0 < c + |u| := add_pos_of_pos_of_nonneg hc (abs_nonneg u)
  have hsqabs : |u| ^ 2 < c ^ 2 := by
    nlinarith [mul_pos ha hb]
  have hsq : u ^ 2 < c ^ 2 := by
    simpa [sq_abs] using hsqabs
  have ht : 0 < 1 - u ^ 2 / c ^ 2 := by
    have hlt : u ^ 2 / c ^ 2 < 1 :=
      (div_lt_iff₀ hcn).2 (by nlinarith)
    linarith
  have hfac :
      boostFactor c u ^ 2 * (1 - u ^ 2 / c ^ 2) = 1 := by
    unfold boostFactor
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt ht)]
    exact div_mul_cancel₀ 1 (ne_of_gt ht)
  have hdiff : 1 - u ^ 2 / c ^ 2 = (c ^ 2 - u ^ 2) / c ^ 2 := by
    field_simp [ne_of_gt hcn]
  have hfac_div :
      boostFactor c u ^ 2 * ((c ^ 2 - u ^ 2) / c ^ 2) = 1 := by
    simpa only [hdiff] using hfac
  have hp_norm :
      ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ] <;> ring
  have hboost_norm :
      ‖boostMomentum c u E p‖ ^ 2 =
        (boostFactor c u * (p 0 - u * E / c ^ 2)) ^ 2 +
        (p 1) ^ 2 + (p 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [boostMomentum, Fin.sum_univ_succ] <;> ring
  have hinner :
      (E - u * p 0) ^ 2 - c ^ 2 * (p 0 - u * E / c ^ 2) ^ 2 =
      ((c ^ 2 - u ^ 2) / c ^ 2) * (E ^ 2 - c ^ 2 * (p 0) ^ 2) := by
    field_simp [ne_of_gt hcn]
    ring
  have hlong :
      (boostFactor c u * (E - u * p 0)) ^ 2 -
      c ^ 2 * (boostFactor c u * (p 0 - u * E / c ^ 2)) ^ 2 =
      E ^ 2 - c ^ 2 * (p 0) ^ 2 := by
    calc
      _ = boostFactor c u ^ 2 *
          ((E - u * p 0) ^ 2 -
            c ^ 2 * (p 0 - u * E / c ^ 2) ^ 2) := by ring
      _ = (boostFactor c u ^ 2 * ((c ^ 2 - u ^ 2) / c ^ 2)) *
          (E ^ 2 - c ^ 2 * (p 0) ^ 2) := by rw [hinner]; ring
      _ = E ^ 2 - c ^ 2 * (p 0) ^ 2 := by rw [hfac_div, one_mul]
  unfold boostEnergy
  rw [hboost_norm, hp_norm]
  nlinarith [hlong]
