-- Prove2me | solution 1 for MassEnergyEquivalence.relMass_properties
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:36:07.139625+00:00
-- url     : https://prove2.me/submissions/ed4c57c3-ffd8-4c75-9e61-77a7c54cecd3

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_MassEnergyEquivalence_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MassEnergyEquivalence Filter Asymptotics Topology

/-- Relativistic mass, kinetic energy and equality at rest. -/
theorem solution (c m : ℝ) (v : Vec3) (hc : 0 < c) (hm : 0 ≤ m)
    (hv : ‖v‖ < c) :
    relMass c m v = m + kineticEnergy c m v / c ^ 2 ∧
      m ≤ relMass c m v ∧
      (0 < m → (relMass c m v = m ↔ v = 0)) := by
  have hcn : 0 < c ^ 2 := sq_pos_of_pos hc
  have hn : 0 ≤ ‖v‖ := norm_nonneg _
  have hs : ‖v‖ ^ 2 < c ^ 2 := by
    have ha : 0 < c - ‖v‖ := sub_pos.mpr hv
    have hb : 0 < c + ‖v‖ := add_pos_of_pos_of_nonneg hc hn
    nlinarith [mul_pos ha hb]
  let t : ℝ := 1 - ‖v‖ ^ 2 / c ^ 2
  have ht : 0 < t := by
    dsimp [t]
    have hh : ‖v‖ ^ 2 / c ^ 2 < 1 :=
      (div_lt_iff₀ hcn).2 (by nlinarith)
    linarith
  have ht_le : t ≤ 1 := by
    dsimp [t]
    have hh : 0 ≤ ‖v‖ ^ 2 / c ^ 2 :=
      div_nonneg (sq_nonneg _) (le_of_lt hcn)
    linarith
  have hsqrtpos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsqrtle : Real.sqrt t ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ht_le
  have hgamma : 1 ≤ lorentzFactor c v := by
    change 1 ≤ 1 / Real.sqrt t
    exact (le_div_iff₀ hsqrtpos).2 (by simpa using hsqrtle)
  have hrm : relMass c m v = lorentzFactor c v * m := by
    simp only [relMass, relEnergy]
    field_simp [ne_of_gt hcn]
  have hfirst :
      relMass c m v = m + kineticEnergy c m v / c ^ 2 := by
    simp only [relMass, kineticEnergy, relEnergy, restEnergy]
    field_simp [ne_of_gt hcn]
    ring
  have hsecond : m ≤ relMass c m v := by
    rw [hrm]
    nlinarith [mul_nonneg (sub_nonneg.mpr hgamma) hm]
  refine ⟨hfirst, hsecond, ?_⟩
  intro hmp
  constructor
  · intro he
    have he' : lorentzFactor c v * m = m := by
      simpa only [hrm] using he
    have hprod : (lorentzFactor c v - 1) * m = 0 := by
      nlinarith [he']
    have hzero : lorentzFactor c v - 1 = 0 :=
      (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hmp)
    have hg1 : lorentzFactor c v = 1 := by linarith
    have heq : (1 : ℝ) / Real.sqrt t = 1 := by
      simpa only [lorentzFactor, t] using hg1
    have hroot : Real.sqrt t = 1 := by
      have hh := (div_eq_iff (ne_of_gt hsqrtpos)).mp heq
      linarith
    have ht1 : t = 1 := by
      nlinarith [Real.sq_sqrt (le_of_lt ht)]
    have hq : ‖v‖ ^ 2 / c ^ 2 = 0 := by
      dsimp [t] at ht1
      linarith
    have hn2 : ‖v‖ ^ 2 = 0 := by
      have hh := (div_eq_iff (ne_of_gt hcn)).mp hq
      nlinarith [hh]
    have hn0 : ‖v‖ = 0 := by nlinarith
    exact norm_eq_zero.mp hn0
  · intro hv0
    subst v
    rw [hrm]
    simp [lorentzFactor]
