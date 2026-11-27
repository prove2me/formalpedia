-- Prove2me | solution 1 for Kyprianou.Ch04.compactDifferenceSquareEnvelopeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:56:14.841941+00:00
-- url     : https://prove2.me/submissions/9e5d0101-3e75-4f77-ac6f-b1759f7c465e

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The square supremum of two bounded compact paths controls their pointwise difference. -/
theorem solution  (Y Z : NNReal → ℝ) (T : NNReal)
    (C D : ℝ) (hY : ∀ t ≤ T, |Y t| ≤ C) (hZ : ∀ t ≤ T, |Z t| ≤ D) :
    let S := sSup ((fun t : NNReal => |Y t-Z t|^2) '' Iic T)
    0 ≤ S ∧ ∀ t ≤ T, |Y t-Z t| ≤ Real.sqrt S := by
  intro S
  have hC : 0 ≤ C := (abs_nonneg _).trans (hY 0 (by positivity))
  have hD : 0 ≤ D := (abs_nonneg _).trans (hZ 0 (by positivity))
  have hb : BddAbove ((fun t : NNReal => |Y t-Z t|^2) '' Iic T) := by
    refine ⟨(C+D)^2,?_⟩
    rintro x ⟨t,ht,rfl⟩
    have h0 : |Y t-Z t| ≤ |Y t|+|Z t| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (Y t) 0 (Z t)
    have h := h0.trans (add_le_add (hY t ht) (hZ t ht))
    nlinarith [abs_nonneg (Y t-Z t)]
  have hs (t : NNReal) (ht : t ≤ T) : |Y t-Z t|^2 ≤ S :=
    le_csSup hb ⟨t,ht,rfl⟩
  have hS : 0 ≤ S := (sq_nonneg _).trans (hs 0 (by positivity))
  refine ⟨hS,fun t ht => ?_⟩
  have hh := hs t ht
  nlinarith [Real.sq_sqrt hS,Real.sqrt_nonneg S,abs_nonneg (Y t-Z t)]
