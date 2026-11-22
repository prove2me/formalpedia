-- Prove2me | solution 1 for LevyStochCalc.Driver.norm_cellHalf_le
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T04:01:00.963802+00:00
-- url     : https://prove2.me/submissions/c53d9609-382c-48e4-bd87-087653b44ff2

import Definitions.Def_LevyStochCalc_Driver_CellGronwallPairing_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairings of a weight with the cell character

The mixed cell lemma runs a Grönwall argument on the pairing of a square-integrable weight and a
bounded factor with the product of the Brownian cell character `e^{i l X_s}` and the Poisson cell
character. That complex pairing is the combination of four real pairings, one for each of the
cosine and sine against the real and imaginary parts of the Poisson character, and equally the
cosine half plus `i` times the sine half, a half being the pairing of a trigonometric function of
the Brownian increment with the Poisson character. This file introduces those pairings together
with their integrability and boundedness, and records the cell identity for a real pairing in the
reduced form that the recombination consumes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Parts

variable (N : PoissonRandomMeasure P ν)

end Parts

section Half

variable (N : PoissonRandomMeasure P ν)

variable {Z V : Ω → ℝ} {Mv l : ℝ} {X : ℝ → Ω → ℝ} {g : ℝ → ℝ}

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}


omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.solution (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (hZ1 : Integrable Z P)
    (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, |V ω| ≤ Mv) (hgb : ∀ x, |g x| ≤ 1) (s : ℝ) :
    ‖cellHalf N w Bfam Z V l X g s‖ ≤ Mv * ∫ ω, ‖Z ω‖ ∂P := by
  unfold cellHalf
  have hb (ω : Ω) : ‖(((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charAt N w Bfam s ω)‖
      ≤ Mv * ‖Z ω‖ := by
    have hc : ‖charAt N w Bfam s ω‖ = 1 := by
      first | exact norm_charAt _ _ _ _ _ | simp [charAt, Complex.norm_exp]
    rw [norm_mul, hc, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
    rw [mul_comm Mv, Real.norm_eq_abs]
    calc
      _ ≤ (|Z ω| * Mv) * 1 := by gcongr; exact hVb ω; exact hgb _
      _ = _ := mul_one _
  calc
    _ ≤ ∫ ω, Mv * ‖Z ω‖ ∂P := norm_integral_le_of_norm_le (hZ1.norm.const_mul Mv) (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_const_mul]
