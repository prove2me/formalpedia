-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.progressivelyMeasurable_mul_indIoc
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:36:13.664336+00:00
-- url     : https://prove2.me/submissions/32cfa9a8-8871-42c8-855a-ca2d0ca3261d

import Definitions.Def_LevyStochCalc_Brownian_ItoPullOut_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pulling a past weight inside an Itô integral over a window

A bounded `ℱ_a`-measurable weight times the Itô integral of an integrand supported in `(a, b]` is
the Itô integral of the weighted integrand: the weight times the indicator is itself a simple
integrand, so this is associativity against a simple integrand.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]



theorem _root_.solution (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M)
    (hVm : Measurable V) (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * indIoc Ω a b ω s := by
  intro t
  by_cases hat : a ≤ t
  · letI : MeasurableSpace Ω := ℱ t
    have hv : StronglyMeasurable V := hVa.mono (ℱ.mono hat)
    let S : Set (Ω × ℝ) := Prod.snd ⁻¹' (Set.Ioc a b ∩ Set.Iic t)
    have hs : MeasurableSet S := measurable_snd (measurableSet_Ioc.inter measurableSet_Iic)
    have hh := (hv.comp_measurable measurable_fst).indicator hs
    convert hh using 1
    funext p
    by_cases ht : p.2 ≤ t <;> by_cases hb : a < p.2 ∧ p.2 ≤ b <;>
      simp [S, indIoc, Set.indicator_apply, ht, hb]
  · have hzero : (fun p : Ω × ℝ =>
        (Set.Iic t).indicator (fun s => V p.1 * indIoc Ω a b p.1 s) p.2) = 0 := by
      funext p
      by_cases ht : p.2 ≤ t
      · have hna : ¬ a < p.2 := not_lt_of_ge (ht.trans (le_of_lt (lt_of_not_ge hat)))
        simp [indIoc, Set.indicator_apply, ht, hna]
      · simp [Set.indicator_apply, ht]
    rw [hzero]
    exact stronglyMeasurable_const
