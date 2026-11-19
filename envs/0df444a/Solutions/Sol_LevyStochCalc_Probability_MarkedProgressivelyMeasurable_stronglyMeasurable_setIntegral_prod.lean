-- Prove2me | solution 1 for LevyStochCalc.Probability.MarkedProgressivelyMeasurable.stronglyMeasurable_setIntegral_prod
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:53:28.217939+00:00
-- url     : https://prove2.me/submissions/3d18f019-ee98-493b-9865-2f21c91df1e7

import Definitions.Def_LevyStochCalc_Probability_Progressive_F002

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
    (hSt : S ⊆ Set.Iic t) (μ : Measure ℝ) [SFinite μ] :
    @StronglyMeasurable (Ω × E) F _ (@Prod.instMeasurableSpace Ω E (ℱ t) inferInstance)
      fun q : Ω × E => ∫ s in S, φ q.1 s q.2 ∂μ := by
  letI : MeasurableSpace Ω := ℱ t
  have hr : Measurable fun r : (Ω × E) × ℝ => (r.1.1, r.2, r.1.2) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have h1 : StronglyMeasurable fun q : Ω × E =>
      ∫ s in S, (Set.Iic t).indicator (fun s => φ q.1 s q.2) s ∂μ :=
    ((h t).comp_measurable hr).integral_prod_right' (ν := μ.restrict S)
  have : (fun q : Ω × E => ∫ s in S, φ q.1 s q.2 ∂μ)
      = fun q : Ω × E => ∫ s in S, (Set.Iic t).indicator (fun s => φ q.1 s q.2) s ∂μ := by
    funext q
    exact setIntegral_congr_fun hS fun s hs =>
      (Set.indicator_of_mem (hSt hs) (fun s => φ q.1 s q.2)).symm
  rw [this]
  exact h1
end MarkedIntegral

/-! ### Countable suprema of real progressively measurable processes -/

section RealLimsup

variable {ℱ : Filtration ℝ mΩ}

end RealLimsup

end LevyStochCalc.Probability
