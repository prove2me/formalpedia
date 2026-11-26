-- Prove2me | solution 1 for Kyprianou.Ch04.finiteSignedPartsHorizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:17:36.617503+00:00
-- url     : https://prove2.me/submissions/8d4ccf54-91a2-4a37-ab4a-eb870a86b4b7

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite expected absolute compensator mass bounds both signed-part masses. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (nu : Measure ℝ) (k : ℝ → ℝ → Omega → ℝ)
    (t : NNReal)
    (hFin : (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal |k s x w| ∂nu ∂volume ∂P) < ⊤) :
    (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (max (k s x w) 0) ∂nu ∂volume ∂P) < ⊤ ∧
    (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (max (-k s x w) 0) ∂nu ∂volume ∂P) < ⊤ := by
  constructor
  · refine lt_of_le_of_lt (lintegral_mono fun w => lintegral_mono fun s =>
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_) hFin
    exact max_le (le_abs_self _) (abs_nonneg _)
  · refine lt_of_le_of_lt (lintegral_mono fun w => lintegral_mono fun s =>
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_) hFin
    exact max_le (neg_le_abs _) (abs_nonneg _)
