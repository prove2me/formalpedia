-- Prove2me | solution 1 for Kyprianou.Ch04.compactSquareSupProbabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:44:21.987726+00:00
-- url     : https://prove2.me/submissions/f0293e18-ebfb-4ee2-98fa-1ef7974f4d06

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Markov's inequality for the actual compact path supremum. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : NNReal → Ω → ℝ) (T : NNReal) (d : ℝ) (hd : 0 < d)
    (hb : ∀ᵐ w ∂P, BddAbove ((fun t : NNReal => |Y t w|^2) '' Iic T))
    (hi : Integrable (fun w => sSup ((fun t : NNReal => |Y t w|^2) '' Iic T)) P) :
    P {w | ∃ t ≤ T, d < |Y t w|} ≤
      ENNReal.ofReal (∫ w, sSup ((fun t : NNReal => |Y t w|^2) '' Iic T) ∂P) /
        ENNReal.ofReal (d^2) := by
  let S : Ω → ℝ := fun w => sSup ((fun t : NNReal => |Y t w|^2) '' Iic T)
  have hn : 0 ≤ᵐ[P] S := by
    filter_upwards [hb] with w hw
    exact (sq_nonneg |Y 0 w|).trans
      (le_csSup hw ⟨0,(show (0 : NNReal) ∈ Iic T by simp),rfl⟩)
  have hsub : ∀ᵐ w ∂P, w ∈ {w | ∃ t ≤ T, d < |Y t w|} →
      w ∈ {w | ENNReal.ofReal (d^2) ≤ ENNReal.ofReal (S w)} := by
    filter_upwards [hb] with w hw
    rintro ⟨t,ht,hgt⟩
    apply ENNReal.ofReal_le_ofReal
    exact (by nlinarith [abs_nonneg (Y t w)] : d^2 ≤ |Y t w|^2).trans
      (le_csSup hw ⟨t,ht,rfl⟩)
  have hm := meas_ge_le_lintegral_div
    (ENNReal.measurable_ofReal.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable)
    (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hd)) ENNReal.ofReal_ne_top
  change P {w | ENNReal.ofReal (d^2) ≤ ENNReal.ofReal (S w)} ≤
    (∫⁻ w, ENNReal.ofReal (S w) ∂P) / ENNReal.ofReal (d^2) at hm
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn] at hm
  exact (measure_mono_ae hsub).trans hm
