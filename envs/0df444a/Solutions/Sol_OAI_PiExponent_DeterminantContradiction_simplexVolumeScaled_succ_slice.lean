-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_slice
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:47:11.727975+00:00
-- url     : https://prove2.me/submissions/8f1f76b3-9cf9-4b65-9d76-b48246f1ea60

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_formula
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_integral_pow
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution (n : Nat) (r : Real) (hr : 0 ≤ r) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ∫⁻ t in Set.Icc (0 : Real) r,
        MeasureTheory.volume
          {y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (∑ j, y j) ≤ r - t}
        ∂MeasureTheory.volume := by
  have hslice :
      (∫⁻ t in Set.Icc (0 : Real) r,
        MeasureTheory.volume
          {y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (∑ j, y j) ≤ r - t}
        ∂MeasureTheory.volume) =
      ∫⁻ t in Set.Icc (0 : Real) r,
        ENNReal.ofReal ((r - t) ^ n / (Nat.factorial n : Real))
        ∂MeasureTheory.volume := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    exact OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_formula
      n (r - t) (sub_nonneg.mpr ht.2)
  calc
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ (n + 1) / (Nat.factorial (n + 1) : Real)) :=
        OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_formula
          (n + 1) r hr
    _ = ∫⁻ t in Set.Icc (0 : Real) r,
        ENNReal.ofReal ((r - t) ^ n / (Nat.factorial n : Real))
        ∂MeasureTheory.volume :=
      (OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_integral_pow
        n r hr).symm
    _ = ∫⁻ t in Set.Icc (0 : Real) r,
        MeasureTheory.volume
          {y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (∑ j, y j) ≤ r - t}
        ∂MeasureTheory.volume := hslice.symm