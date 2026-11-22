-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.sq_enorm_finsetSum_le
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:42:09.92767+00:00
-- url     : https://prove2.me/submissions/744550d5-e6f6-48df-aa06-294192575511

import Definitions.Def_LevyStochCalc_Brownian_ItoTruncate_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncating an integrand to a bounded one

Clamping a real integrand to `[-j, j]` leaves a bounded integrand that approximates it in energy:
the clamp is `1`-Lipschitz, fixes `0`, never increases the absolute value, and converges to the
identity pointwise, so dominated convergence gives energy convergence on every window.

## Main statements

* `LevyStochCalc.clampAt` — the clamp.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_clampAt_sub` — the clamped integrand converges to
  the integrand in energy.
-/

namespace LevyStochCalc

open MeasureTheory
open scoped NNReal ENNReal Topology

section Clamp

end Clamp

namespace Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Difference

open LevyStochCalc.Brownian.Multidim

variable {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)



theorem _root_.solution {m : ℕ} (x : Fin m → ℝ) :
    (‖∑ k, x k‖₊ : ℝ≥0∞) ^ 2 ≤ (m : ℝ≥0∞) * ∑ k, (‖x k‖₊ : ℝ≥0∞) ^ 2 := by
  have ha : |∑ k, x k| ≤ ∑ k, |x k| := Finset.abs_sum_le_sum_abs _ _
  have h1 := pow_le_pow_left₀ (abs_nonneg (∑ k, x k)) ha 2
  have h2 := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin m)))
    (f := fun k => |x k|) (fun k _ => abs_nonneg (x k)) 1
  have hr : |∑ k, x k| ^ 2 ≤ (m : ℝ) * ∑ k, |x k| ^ 2 := by
    exact h1.trans (by simpa using h2)
  have hn : ‖∑ k, x k‖₊ ^ 2 ≤ (m : ℝ≥0) * ∑ k, ‖x k‖₊ ^ 2 := by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_sum,
      coe_nnnorm, Real.norm_eq_abs] using hr
  exact_mod_cast hn
