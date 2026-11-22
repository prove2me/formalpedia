-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_sq_sub_le_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:51:39.61385+00:00
-- url     : https://prove2.me/submissions/939068df-1e14-4e91-984c-c63ec4130888

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The uniform grid and the third-moment remainder

The uniform partition of `[0, T]` into `m` cells, and the bound it gives for the sum of third
absolute moments of the increments of an Itô process — the size of the Taylor remainder in
Itô's formula.

## Main statements

* `LevyStochCalc.Brownian.Ito.unifGrid` — the uniform grid on `[0, T]`.
* `LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid` — the simple integrand carried by
  the uniform grid.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_sub_pow_three_le` — the sum of third absolute
  moments of the Itô-integral increments across the grid, of order `m^{-1/2}`.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_itoIncrement_pow_three_le` — the same for the
  increments of a full Itô process, drift included.
* `LevyStochCalc.Brownian.Ito.tendsto_riemann_weighted_unifGrid` — the Riemann sums of a
  continuous weight against a bounded density converge as the grid refines.
* `LevyStochCalc.Brownian.Ito.exists_unifGrid_cell` — every time in `(0, T]` lies in a cell.
* `LevyStochCalc.Brownian.Ito.abs_ofUnifGrid_eval_sub_le` — the grid step weight is within the
  weight's modulus of continuity at the mesh.
* `LevyStochCalc.Brownian.Ito.lintegral_sq_sub_le_of_bound` — a uniform pathwise bound on
  `(0, T]` gives the `L²` distance over the window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section ThirdMomentSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end ThirdMomentSum



theorem _root_.solution {P : Measure Ω} [IsProbabilityMeasure P]
    (u v : Ω → ℝ → ℝ) {ε T : ℝ} (hε0 : 0 ≤ ε)
    (hbound : ∀ (ω : Ω), ∀ s ∈ Set.Ioc (0 : ℝ) T, |u ω s - v ω s| ≤ ε) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (ε ^ 2 * T) := by
  have hmeas : volume.restrict (Set.Icc (0 : ℝ) T) = volume.restrict (Set.Ioc 0 T) := by
    exact Measure.restrict_congr_set (Ioc_ae_eq_Icc.symm)
  rw [hmeas]
  let C : ℝ≥0 := ⟨ε, hε0⟩
  calc
    _ ≤ ∫⁻ _ : Ω, ∫⁻ _ in Set.Ioc (0 : ℝ) T, (C : ℝ≥0∞) ^ 2 ∂volume ∂P := by
      apply lintegral_mono
      intro ω
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have h : ‖u ω s - v ω s‖₊ ≤ C := by
        change (‖u ω s - v ω s‖₊ : ℝ) ≤ ε
        simpa only [coe_nnnorm, Real.norm_eq_abs] using hbound ω s hs
      exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr h) 2
    _ = _ := by
      rw [lintegral_const, lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
      simp only [measure_univ, mul_one]
      rw [ENNReal.ofReal_mul (sq_nonneg ε)]
      congr 1
      rw [ENNReal.ofReal_pow hε0]
      change (C : ℝ≥0∞) ^ 2 = ENNReal.ofReal (C : ℝ) ^ 2
      rw [ENNReal.ofReal_coe_nnreal]
