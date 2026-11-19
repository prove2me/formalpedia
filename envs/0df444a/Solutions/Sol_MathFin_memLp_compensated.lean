-- Prove2me | solution 1 for MathFin.memLp_compensated
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:03:02.569319+00:00
-- url     : https://prove2.me/submissions/0d43c3bd-7dc7-4659-bde6-deb15dbed599

import Definitions.Def_MathFin_Foundations_PoissonRandomMeasure_F000

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/

/-!
# Poisson random measure and the compensated increment

A *Poisson random measure* `N` on the time-mark space `[0, ∞) × E` with σ-finite
mark-intensity `ν` is the driving object of Lévy-driven stochastic calculus: `N(·, B)`
is `Poisson`-distributed with mean `ν̂(B)` (`ν̂ := Leb[0,∞) ⊗ ν`), and counts on disjoint
regions are independent. The *compensated* measure `Ñ(B) := N(B) − ν̂(B)` is the mean-zero,
`L²` object one integrates against.

This module provides the object as a hypothesis-bundling structure (its fields are the
Applebaum Def. 2.3.1 properties) plus the two Poisson moment facts the isometry needs —
`𝔼[N(B)] = ν̂(B)` and `𝔼[N(B)²] = ν̂(B)² + ν̂(B)` — hence `𝔼[Ñ(B)] = 0`, `𝔼[Ñ(B)²] = ν̂(B)`.

Mathlib carries the Poisson law (`poissonMeasure`, `integral_poissonMeasure`)
but *not* its mean or variance; we derive them here from the total-mass identity by a single
index shift (`(n+1)·pmf(n+1) = r·pmf(n)`), with no exp-series differentiation.

## Provenance

The `PoissonRandomMeasure` structure's field shape is consulted from
`cgarryZA/LevyStochCalc` (Apache-2.0), itself a faithful rendering of Applebaum Def. 2.3.1;
the isometry developed on top (see `PoissonCompensatedIsometryAdapted` / `…IntegralL2`) is our
own — LevyStochCalc states that isometry as its cited axiom #6, we prove it. References:
Applebaum, *Lévy Processes and Stochastic Calculus*, CUP 2009, Def. 2.3.1 / Thm 4.2.3.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-! ## §1  Moments of the scalar Poisson law (Mathlib gap-fill) -/

/-! ## §2  The Poisson random measure and its compensated increment -/

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]

/-! ### Compensated-increment moments (transport of the scalar moments through `poisson_law`) -/

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]



theorem _root_.solution (N : PoissonRandomMeasure P ν) {D : Set (ℝ × E)}
    (hD : MeasurableSet D) (hfin : referenceIntensity ν D ≠ ⊤) :
    MemLp (N.compensated D) 2 P := by
  set c : ℝ := (referenceIntensity ν D).toReal with hc
  set r : ℝ≥0 := (referenceIntensity ν D).toNNReal with hr
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hX : Measurable (fun ω => N.N ω D) := N.measurable_eval hD
  have hmeas : AEStronglyMeasurable (N.compensated D) P :=
    (N.measurable_compensated hD).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hg : Measurable (fun x : ℝ≥0∞ => (x.toReal - c) ^ 2) := by fun_prop
  have h1 : Integrable (fun x : ℝ≥0∞ => (x.toReal - c) ^ 2) (P.map (fun ω => N.N ω D)) := by
    rw [N.poisson_law hD hfin, poissonMeasureENN,
      integrable_map_measure hg.aestronglyMeasurable (by fun_prop)]
    rw [integrable_poissonMeasure_iff]
    have hs : Summable (fun n : ℕ =>
        2 * Real.exp (c - r) * (((r : ℝ) * Real.exp 1) ^ n / (n.factorial : ℝ))) :=
      (Real.summable_pow_div_factorial _).mul_left _
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
    simp only [Function.comp_apply, ENNReal.toReal_natCast]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hsq : ‖((n : ℝ) - c) ^ 2‖ ≤ 2 * Real.exp ((n : ℝ) + c) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have := Real.pow_div_factorial_le_exp (x := (n : ℝ) + c) (by positivity) 2
      simp only [Nat.factorial_two, Nat.cast_ofNat] at this
      nlinarith
    have he1 : Real.exp ((n : ℝ) + c) = Real.exp 1 ^ n * Real.exp c := by
      rw [Real.exp_add, ← Real.exp_nat_mul, mul_one]
    have he2 : Real.exp (c - r) = Real.exp c * Real.exp (-(r : ℝ)) := by
      rw [sub_eq_add_neg, Real.exp_add]
    calc Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) * ‖((n : ℝ) - c) ^ 2‖
        ≤ Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) * (2 * Real.exp ((n : ℝ) + c)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 2 * Real.exp (c - r) * (((r : ℝ) * Real.exp 1) ^ n / (n.factorial : ℝ)) := by
          rw [he1, he2, mul_pow]; ring
  have h2 := (integrable_map_measure hg.aestronglyMeasurable hX.aemeasurable).1 h1
  simpa [Function.comp_def, PoissonRandomMeasure.compensated, hc] using h2

