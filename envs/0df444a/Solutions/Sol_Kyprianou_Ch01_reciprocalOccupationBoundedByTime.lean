-- Prove2me | solution 1 for Kyprianou.Ch01.reciprocalOccupationBoundedByTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:44:11.523417+00:00
-- url     : https://prove2.me/submissions/a194955c-573d-4748-8718-62cbc10f5854

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.NNReal.Basic
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Positive integer paths have inverse-speed occupation clock at most t. -/
theorem solution {Ω : Type*} (X : NNReal → Ω → ℤ) (ω : Ω)
    (t : NNReal) (hpositive : ∀ s : NNReal, s ≤ t → 0 < X s ω) :
    reciprocalOccupation X t ω ≤ ENNReal.ofReal (t : ℝ) := by
  have hbound (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) (t : ℝ)) :
      (ENNReal.ofReal (X (Real.toNNReal s) ω : ℝ))⁻¹ ≤ 1 := by
    have hsle : s ≤ (t : ℝ) := hs.2
    have hst : Real.toNNReal s ≤ t := by
      simpa only [Real.toNNReal_coe] using
        (Real.toNNReal_le_toNNReal hsle)
    have hp : 0 < X (Real.toNNReal s) ω := hpositive _ hst
    have hnat : 1 ≤ X (Real.toNNReal s) ω := by omega
    have hr : (1 : ℝ) ≤ (X (Real.toNNReal s) ω : ℝ) := by
      exact_mod_cast hnat
    have he : (1 : ENNReal) ≤
        ENNReal.ofReal (X (Real.toNNReal s) ω : ℝ) := by
      calc
        (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by norm_num
        _ ≤ _ := ENNReal.ofReal_le_ofReal hr
    simpa only [inv_one] using (ENNReal.inv_le_inv' he)
  unfold reciprocalOccupation
  calc
    (∫⁻ s in Set.Ioc (0 : ℝ) (t : ℝ),
      (ENNReal.ofReal (X (Real.toNNReal s) ω : ℝ))⁻¹ ∂volume) ≤
        ∫⁻ _s in Set.Ioc (0 : ℝ) (t : ℝ), (1 : ENNReal) ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact hbound s hs
    _ = ENNReal.ofReal (t : ℝ) := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
          simp
