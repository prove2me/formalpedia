-- Prove2me | solution 1 for Kyprianou.Ch04.terminalCauchyFromCompactSupV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:05:08.807791+00:00
-- url     : https://prove2.me/submissions/eb60a4a7-6cd9-4526-8715-0402907b68c3

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- A compact squared-supremum Cauchy estimate implies terminal square Cauchy. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℝ → NNReal → Ω → ℝ)
    (hi : ∀ a, 0 < a → a < 1 → ∀ t,
      Measurable (Y a t) ∧ Integrable (fun w => (Y a t w)^2) P)
    (hc : ∀ T : NNReal, 0 < T → ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ a b, 0 < a → a < r → 0 < b → b < r →
        (∀ᵐ w ∂P, BddAbove ((fun t : NNReal => |Y a t w - Y b t w|^2) '' Iic T)) ∧
        Integrable (fun w => sSup ((fun t : NNReal => |Y a t w - Y b t w|^2) '' Iic T)) P ∧
        (∫ w, sSup ((fun t : NNReal => |Y a t w - Y b t w|^2) '' Iic T) ∂P) < δ) :
    ∀ t : NNReal, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ a b, 0 < a → a < r → 0 < b → b < r →
        (∫ w, (Y a t w - Y b t w)^2 ∂P) ≤ δ := by
  intro t δ hd
  obtain ⟨r,hr,hr1,h⟩ := hc (t+1) (by positivity) δ hd
  refine ⟨r,hr,hr1,?_⟩
  intro a b ha har hb hbr
  obtain ⟨hB,hI,hD⟩ := h a b ha har hb hbr
  have hA := hi a ha (har.trans hr1) t
  have hB' := hi b hb (hbr.trans hr1) t
  have hSq := (((memLp_two_iff_integrable_sq hA.1.aestronglyMeasurable).mpr hA.2).sub
    ((memLp_two_iff_integrable_sq hB'.1.aestronglyMeasurable).mpr hB'.2)).integrable_sq
  apply le_trans (integral_mono_ae hSq hI ?_) hD.le
  filter_upwards [hB] with w hw
  have hh := le_csSup hw ⟨t,(show t ∈ Iic (t+1) by simp),rfl⟩
  change (Y a t w - Y b t w)^2 ≤ _
  simpa only [sq_abs] using hh
