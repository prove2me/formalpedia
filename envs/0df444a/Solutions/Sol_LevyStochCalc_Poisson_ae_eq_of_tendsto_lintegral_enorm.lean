-- Prove2me | solution 1 for LevyStochCalc.Poisson.ae_eq_of_tendsto_lintegral_enorm
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T04:07:27.983112+00:00
-- url     : https://prove2.me/submissions/e074c5c6-185d-4cf9-9a76-d41b71c819d8

import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From energy to the mean pathwise integral

The compensator identity turns the mean of the absolute integral against the random measure into
the mean against the reference intensity, and on a window of finite intensity the latter is
controlled by the energy through the comparison of `L¹` with `L²`. So an energy-null sequence of
predictable marked integrands has pathwise compensated integrals tending to zero in mean.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Bound

variable {A : Set E} {T : ℝ}


omit [IsProbabilityMeasure P] in

theorem _root_.solution {Y Z : Ω → ℝ} {X : ℕ → Ω → ℝ}
    (hY : AEStronglyMeasurable Y P) (hZ : AEStronglyMeasurable Z P)
    (hX : ∀ n, AEStronglyMeasurable (X n) P)
    (h1 : Tendsto (fun n => ∫⁻ ω, ‖Y ω - X n ω‖ₑ ∂P) atTop (𝓝 0))
    (h2 : Tendsto (fun n => ∫⁻ ω, ‖X n ω - Z ω‖ₑ ∂P) atTop (𝓝 0)) :
    Y =ᵐ[P] Z := by
  have hle (n : ℕ) : (∫⁻ ω, ‖Y ω - Z ω‖ₑ ∂P) ≤
      (∫⁻ ω, ‖Y ω - X n ω‖ₑ ∂P) + ∫⁻ ω, ‖X n ω - Z ω‖ₑ ∂P := by
    have hm : AEMeasurable (fun ω => ‖Y ω - X n ω‖ₑ) P := (hY.sub (hX n)).aemeasurable.enorm
    rw [← lintegral_add_left' hm]
    apply lintegral_mono
    intro ω
    change ‖Y ω - Z ω‖ₑ ≤ ‖Y ω - X n ω‖ₑ + ‖X n ω - Z ω‖ₑ
    rw [show Y ω - Z ω = (Y ω - X n ω) + (X n ω - Z ω) by ring]
    exact enorm_add_le _ _
  have ht := h1.add h2
  rw [add_zero] at ht
  have hz : (∫⁻ ω, ‖Y ω - Z ω‖ₑ ∂P) = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds ht hle) bot_le
  have h := (lintegral_eq_zero_iff' (hY.sub hZ).aemeasurable.enorm).mp hz
  filter_upwards [h] with ω hω
  exact sub_eq_zero.mp (by simpa using hω)
