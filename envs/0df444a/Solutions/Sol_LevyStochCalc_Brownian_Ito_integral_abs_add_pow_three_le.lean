-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_abs_add_pow_three_le
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:46:28.437644+00:00
-- url     : https://prove2.me/submissions/157b950c-d1cc-45c2-baa1-b0b387da4d4f

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F001

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



theorem _root_.solution {P : Measure Ω} {u v : Ω → ℝ}
    (hu : MeasureTheory.Integrable (fun ω => |u ω| ^ 3) P)
    (hv : MeasureTheory.Integrable (fun ω => |v ω| ^ 3) P)
    (huv : MeasureTheory.Integrable (fun ω => |u ω + v ω| ^ 3) P) :
    ∫ ω, |u ω + v ω| ^ 3 ∂P ≤ 4 * ((∫ ω, |u ω| ^ 3 ∂P) + ∫ ω, |v ω| ^ 3 ∂P) := by
  have hp (ω : Ω) : |u ω + v ω| ^ 3 ≤ 4 * (|u ω| ^ 3 + |v ω| ^ 3) := by
    have h₁ := pow_le_pow_left₀ (abs_nonneg (u ω + v ω)) (abs_add_le (u ω) (v ω)) 3
    have h₂ := mul_nonneg (sq_nonneg (|u ω| - |v ω|)) (add_nonneg (abs_nonneg (u ω)) (abs_nonneg (v ω)))
    nlinarith
  calc
    _ ≤ ∫ ω, 4 * (|u ω| ^ 3 + |v ω| ^ 3) ∂P :=
      integral_mono huv ((hu.add hv).const_mul 4) hp
    _ = _ := by rw [integral_const_mul, integral_add hu hv]
