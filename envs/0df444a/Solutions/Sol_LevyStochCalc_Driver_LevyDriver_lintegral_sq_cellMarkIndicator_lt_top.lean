-- Prove2me | solution 1 for LevyStochCalc.Driver.LevyDriver.lintegral_sq_cellMarkIndicator_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:46:28.499806+00:00
-- url     : https://prove2.me/submissions/a9d17f84-061b-4509-8e60-428a00c93d97

import Definitions.Def_LevyStochCalc_Driver_CellConditionalIsometryPoisson_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Conditional cell isometries against the compensated Poisson random measure

Over a cell `(a, b]` with `0 ≤ a < b` and a mark set `A` of finite intensity, the increment of a
compensated integral across `(a, b]` pairs with the compensated count `Ñ((a, b] × A)` to the
integral of the integrand over the cell and over `A`, and the pairing survives conditioning at
the left endpoint. The compensated count is the compensated integral of the indicator integrand
of the rectangle `(a, b] × A`, restricting the integrand to the cell turns the increment into the
integral at the horizon `b`, a bounded weight measurable at `a` passes inside, and the horizon
isometry then evaluates the pairing.

## Main statements

* `stochasticIntegral_cellMarkIndicator_ae_eq` — the compensated count of `(a, b] × A` is the
  compensated integral of the indicator integrand of that rectangle.
* `condExp_compensated_cell_mul_compensated_count` — the conditional Itô–Lévy isometry over a
  cell, against the compensated count of `(a, b] × A`.
* `condExp_brownian_cell_mul_compensated_count_eq_zero` — a Brownian cell increment is
  conditionally orthogonal to the compensated count of `(a, b] × A`.

## References

* Karatzas and Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §3.2.
* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open LevyStochCalc.Brownian.Ito (indIoc)

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section CompensatedCell

variable {φ : Ω → ℝ → E → ℝ} {A : Set E}


omit [SigmaFinite ν] in

theorem _root_.solution (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (a b : ℝ) : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖cellMarkIndicator Ω a b A ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  intro T hT
  have hle (ω : Ω) (s : ℝ) (e : E) :
      (‖cellMarkIndicator Ω a b A ω s e‖₊ : ℝ≥0∞) ^ 2 ≤
        A.indicator (fun _ => (1 : ℝ≥0∞)) e := by
    by_cases he : e ∈ A <;> by_cases hs : s ∈ Set.Ioc a b <;>
      simp [cellMarkIndicator, Set.indicator_apply, he, hs, Set.mem_Ioc] at *
  calc
    _ ≤ ∫⁻ _ : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ∫⁻ e, A.indicator (fun _ => (1 : ℝ≥0∞)) e ∂ν ∂volume ∂P := by
      exact lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono (hle ω s)
    _ < ⊤ := by
      simp only [lintegral_indicator hA, lintegral_const, one_mul,
        measure_univ, mul_one, Real.volume_Icc, sub_zero, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top hAν.lt_top ENNReal.ofReal_lt_top
