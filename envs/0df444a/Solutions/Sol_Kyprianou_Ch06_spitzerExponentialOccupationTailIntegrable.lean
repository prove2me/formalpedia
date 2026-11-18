-- Prove2me | solution 1 for Kyprianou.Ch06.spitzerExponentialOccupationTailIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:36:57.575459+00:00
-- url     : https://prove2.me/submissions/969da3d9-2982-4884-b39c-b42e52bcb88f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false

theorem solution
    (p : Real) (hp : 0 < p)
    (f : Real → Real) (hf : Measurable f)
    (hfBound : ∀ t ∈ Set.Ioi (1 : Real), 0 ≤ f t ∧ f t ≤ 1) :
    IntegrableOn
      (fun t : Real => Real.exp (-p * t) * f t / t)
      (Set.Ioi (1 : Real)) := by
  have hneg : -p < 0 := neg_lt_zero.mpr hp
  have hExp : IntegrableOn
      (fun t : Real => Real.exp (-p * t))
      (Set.Ioi (1 : Real)) := by
    simpa using
      (integrableOn_exp_mul_Ioi (a := -p) hneg (1 : Real))
  have hMeas : Measurable
      (fun t : Real => Real.exp (-p * t) * f t / t) := by
    have hArg : Measurable (fun t : Real => -p * t) :=
      measurable_const.mul measurable_id
    exact ((Real.measurable_exp.comp hArg).mul hf).div measurable_id
  apply hExp.mono' hMeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hpos : 0 < t := lt_trans (by norm_num : (0 : Real) < 1) ht
  have hOne : (1 : Real) ≤ t := le_of_lt ht
  obtain ⟨hf0, hf1⟩ := hfBound t ht
  have he0 : 0 ≤ Real.exp (-p * t) := le_of_lt (Real.exp_pos _)
  have hnum : 0 ≤ Real.exp (-p * t) * f t :=
    mul_nonneg he0 hf0
  have hdiv : 0 ≤ Real.exp (-p * t) * f t / t :=
    div_nonneg hnum (le_of_lt hpos)
  simp only [Real.norm_eq_abs, abs_of_nonneg hdiv,
    abs_of_nonneg he0]
  apply (div_le_iff₀ hpos).mpr
  calc
    Real.exp (-p * t) * f t ≤ Real.exp (-p * t) * 1 :=
      mul_le_mul_of_nonneg_left hf1 he0
    _ ≤ Real.exp (-p * t) * t :=
      mul_le_mul_of_nonneg_left hOne he0
