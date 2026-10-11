-- Prove2me | solution 1 for MassEnergyEquivalence.energy_momentum_relation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:42:35.569109+00:00
-- url     : https://prove2.me/submissions/913f052e-e671-4138-8dd0-e5df6452c674

import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_MassEnergyEquivalence_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MassEnergyEquivalence Filter Asymptotics Topology

/-- For subluminal velocity, the relativistic energy and momentum satisfy
the Lorentz-invariant mass shell identity. -/
theorem solution (c m : ℝ) (v : Vec3) (hc : 0 < c) (hm : 0 ≤ m)
    (hv : ‖v‖ < c) :
    relEnergy c m v ^ 2 - ‖relMomentum c m v‖ ^ 2 * c ^ 2 = m ^ 2 * c ^ 4 := by
  have hcn : 0 < c ^ 2 := sq_pos_of_pos hc
  have hvn : 0 ≤ ‖v‖ := norm_nonneg _
  have hsq : ‖v‖ ^ 2 < c ^ 2 := by
    have ha : 0 < c - ‖v‖ := sub_pos.mpr hv
    have hb : 0 < c + ‖v‖ := add_pos_of_pos_of_nonneg hc hvn
    nlinarith [mul_pos ha hb]
  have ht : 0 < 1 - ‖v‖ ^ 2 / c ^ 2 := by
    have hlt : ‖v‖ ^ 2 / c ^ 2 < 1 :=
      (div_lt_iff₀ hcn).2 (by nlinarith)
    linarith
  have hgamma :
      lorentzFactor c v ^ 2 * (1 - ‖v‖ ^ 2 / c ^ 2) = 1 := by
    unfold lorentzFactor
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt ht)]
    exact div_mul_cancel₀ 1 (ne_of_gt ht)
  have hgamma_c :
      lorentzFactor c v ^ 2 * (c ^ 2 - ‖v‖ ^ 2) = c ^ 2 := by
    have hdiff :
        1 - ‖v‖ ^ 2 / c ^ 2 = (c ^ 2 - ‖v‖ ^ 2) / c ^ 2 := by
      field_simp [ne_of_gt hcn]
    rw [hdiff] at hgamma
    have hh :
        (lorentzFactor c v ^ 2 * (c ^ 2 - ‖v‖ ^ 2)) / c ^ 2 = 1 := by
      calc
        _ = lorentzFactor c v ^ 2 * ((c ^ 2 - ‖v‖ ^ 2) / c ^ 2) := by ring
        _ = 1 := hgamma
    simpa only [one_mul] using (div_eq_iff (ne_of_gt hcn)).mp hh
  have hmom :
      ‖relMomentum c m v‖ ^ 2 =
        (lorentzFactor c v * m) ^ 2 * ‖v‖ ^ 2 := by
    simp only [relMomentum, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [relEnergy, hmom]
  calc
    (lorentzFactor c v * m * c ^ 2) ^ 2 -
        (lorentzFactor c v * m) ^ 2 * ‖v‖ ^ 2 * c ^ 2 =
      m ^ 2 * c ^ 2 *
        (lorentzFactor c v ^ 2 * (c ^ 2 - ‖v‖ ^ 2)) := by ring
    _ = m ^ 2 * c ^ 2 * c ^ 2 := by rw [hgamma_c]
    _ = m ^ 2 * c ^ 4 := by ring
