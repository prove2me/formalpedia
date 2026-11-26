-- Prove2me | solution 1 for Kyprianou.Ch05.renewalLocalFiniteFromGrowth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:25:23.036935+00:00
-- url     : https://prove2.me/submissions/200a05fc-9946-40da-b8c5-50b87168aab8

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheorem_unrestrictedGrowth
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Renewal measure finite on bounded nonnegative intervals. -/
theorem solution
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F) :
    ∀ x : Real, renewalMeasure F (Set.Icc 0 x) ≠ ⊤ := by
  have hg := classicalRenewalTheorem_unrestrictedGrowth F hSupport hFiniteMean hPositiveMean
  have hpos : 0 < 1 / (∫ x : Real, x ∂F) := one_div_pos.mpr hPositiveMean
  have he : ∀ᶠ t : Real in atTop,
      0 < (renewalMeasure F (Set.Icc 0 t)).toReal / t :=
    hg.eventually (lt_mem_nhds hpos)
  obtain ⟨R, hR⟩ := eventually_atTop.1 he
  intro x
  let y := max x R
  have hy := hR y (le_max_right x R)
  have hf : renewalMeasure F (Set.Icc 0 y) ≠ ⊤ := by
    intro ht
    rw [ht, ENNReal.toReal_top, zero_div] at hy
    exact (lt_irrefl 0) hy
  exact ne_top_of_le_ne_top hf (measure_mono (Icc_subset_Icc_right (le_max_left x R)))
