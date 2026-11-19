-- Prove2me | solution 1 for LevyStochCalc.Probability.MarkedProgressivelyMeasurable.stronglyMeasurable_setIntegral_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:53:51.648382+00:00
-- url     : https://prove2.me/submissions/25b38144-2c2b-4e56-80f6-0de9592df1d4

import Theorems.Thm_LevyStochCalc_Probability_MarkedProgressivelyMeasurable_stronglyMeasurable_setIntegral_prod

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Progressively measurable real processes

`ProgressivelyMeasurable ℱ H` says that the process `H : Ω → ℝ → E`, viewed as a function of
`(ω, s)`, is `ℱ t ⊗ Borel`-measurable on the time window `s ≤ t`, for every `t`. This is
the progressive measurability of Mathlib's `IsStronglyProgressive`, phrased on `Ω × ℝ` by
truncating the time variable at `t`, which is the form in which the stochastic integrals of
this library consume it; `isStronglyProgressive` and `of_isStronglyProgressive` relate the
two.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω}

section General

variable [TopologicalSpace E] [Zero E] [TopologicalSpace F] [Zero F]

namespace ProgressivelyMeasurable

variable {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}

end ProgressivelyMeasurable

end General

section Mul

variable [TopologicalSpace E] [MulZeroClass E] [ContinuousMul E] {ℱ : Filtration ℝ mΩ}

end Mul

section Add

variable [NormedAddCommGroup E] {ℱ : Filtration ℝ mΩ}

end Add

section Integral

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}

end Integral

section Marked

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace F] [Zero F]

namespace MarkedProgressivelyMeasurable

variable {ℱ : Filtration ℝ mΩ} {φ : Ω → ℝ → E → F}

end MarkedProgressivelyMeasurable

end Marked

section MarkedIntegral

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ℱ : Filtration ℝ mΩ} {φ : Ω → ℝ → E → F}


theorem _root_.solution
    (h : MarkedProgressivelyMeasurable ℱ φ) {t : ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hSt : S ⊆ Set.Iic t) (μ : Measure ℝ) [SFinite μ] (ν : Measure E) [SFinite ν] :
    StronglyMeasurable[ℱ t] fun ω => ∫ s in S, ∫ e, φ ω s e ∂ν ∂μ := by
  letI : MeasurableSpace Ω := ℱ t
  have h1 : StronglyMeasurable fun r : (Ω × ℝ) × E =>
      (Set.Iic t).indicator (fun s => φ r.1.1 s r.2) r.1.2 :=
    (h t).comp_measurable MeasurableEquiv.prodAssoc.measurable
  have h2 : StronglyMeasurable fun ω =>
      ∫ s in S, ∫ e, (Set.Iic t).indicator (fun s => φ ω s e) s ∂ν ∂μ :=
    (h1.integral_prod_right' (ν := ν)).integral_prod_right' (ν := μ.restrict S)
  have : (fun ω => ∫ s in S, ∫ e, φ ω s e ∂ν ∂μ)
      = fun ω => ∫ s in S, ∫ e, (Set.Iic t).indicator (fun s => φ ω s e) s ∂ν ∂μ := by
    funext ω
    refine setIntegral_congr_fun hS fun s hs => ?_
    simp only [Set.indicator_of_mem (hSt hs)]
  rw [this]
  exact h2
end MarkedIntegral

/-! ### Countable suprema of real progressively measurable processes -/

section RealLimsup

variable {ℱ : Filtration ℝ mΩ}

end RealLimsup

end LevyStochCalc.Probability
