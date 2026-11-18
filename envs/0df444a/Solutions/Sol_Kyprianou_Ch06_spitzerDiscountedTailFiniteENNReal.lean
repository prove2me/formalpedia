-- Prove2me | solution 1 for Kyprianou.Ch06.spitzerDiscountedTailFiniteENNReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:53:18.186141+00:00
-- url     : https://prove2.me/submissions/a201798e-54aa-454f-8521-10ac9fa2ab36

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_spitzerExponentialOccupationTailIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (p : Real) (hp : 0 < p)
    (f : Real → Real) (hf : Measurable f)
    (hfBound : ∀ t ∈ Set.Ioi (1 : Real), 0 ≤ f t ∧ f t ≤ 1) :
    (∫⁻ t in Set.Ioi (1 : Real),
      ENNReal.ofReal (Real.exp (-p * t) * f t / t) ∂volume) < ⊤ := by
  have hReal :=
    Kyprianou.Ch06.spitzerExponentialOccupationTailIntegrable
      p hp f hf hfBound
  have hMeas :
      Measurable (fun t : Real => Real.exp (-p * t) * f t / t) := by
    have hArg : Measurable (fun t : Real => -p * t) :=
      measurable_const.mul measurable_id
    exact ((Real.measurable_exp.comp hArg).mul hf).div measurable_id
  have hNonneg : ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : Real))),
      0 ≤ Real.exp (-p * t) * f t / t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans (by norm_num : (0 : Real) < 1) ht
    have h0 : 0 ≤ f t := (hfBound t ht).1
    exact div_nonneg (mul_nonneg (le_of_lt (Real.exp_pos _)) h0)
      (le_of_lt ht0)
  have hFinite :
      (∫⁻ t,
        ENNReal.ofReal (Real.exp (-p * t) * f t / t)
        ∂(volume.restrict (Set.Ioi (1 : Real)))) ≠ ⊤ := by
    exact (lintegral_ofReal_ne_top_iff_integrable
      hMeas.aestronglyMeasurable hNonneg).2 hReal
  exact lt_top_iff_ne_top.mpr hFinite
