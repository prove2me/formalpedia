-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integrable_abs_sum_pow_three
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:45:44.410424+00:00
-- url     : https://prove2.me/submissions/2bab4278-2921-4485-96a3-190558fb5251

import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcess_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Vector Itô processes and the moments of their increments

A vector Itô process is `X_t = X₀ + ∫_{[0,t]} b_s ds + ∑ₖ ∫_0^t H^{·,k}_s dWᵏ_s` with values in
`Fin n → ℝ`, driven by a `d`-dimensional Brownian motion. Each coordinate's increment across a
window is a drift increment plus a finite sum of Itô-integral increments, so its moments follow
from the drift bound, the increment moments of the scalar Itô integral and Jensen's inequality
for sums; the supremum norm on `Fin n → ℝ` is then controlled coordinatewise.

## Main statements

* `LevyStochCalc.Brownian.Ito.vectorItoProcess` — the process itself.
* `LevyStochCalc.Brownian.Ito.vectorItoProcess_sub` — the coordinate increment splits into a
  drift part and a sum of Itô-integral increments.
* `LevyStochCalc.Brownian.Ito.integral_sq_vectorItoProcess_sub_le` — the coordinate second
  moment `𝔼|ΔXᵐ|² ≤ 2(BΔt)² + 2d²C²Δt`.
* `LevyStochCalc.Brownian.Ito.integral_abs_vectorItoProcess_sub_le` — the coordinate first
  absolute moment `𝔼|ΔXᵐ| ≤ BΔt + dC√(Δt)`.
* `LevyStochCalc.Brownian.Ito.integral_norm_vectorItoProcess_sub_le` and
  `LevyStochCalc.Brownian.Ito.integral_sq_norm_vectorItoProcess_sub_le` — the same two moments
  for the supremum norm of the vector increment.
* `LevyStochCalc.Brownian.Ito.integrable_norm_vectorItoProcess_sub_pow_three` — the cube of the
  norm of the increment is integrable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section PiNorm

variable {n : ℕ}

end PiNorm

section FiniteSums

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} [Fintype ι]



theorem _root_.solution {f : ι → Ω → ℝ} (hfm : ∀ i, Measurable (f i))
    (hfi : ∀ i, Integrable (fun ω => |f i ω| ^ 3) P) :
    Integrable (fun ω => |∑ i, f i ω| ^ 3) P := by
  classical
  have hm : Measurable (fun ω => |∑ i, f i ω| ^ 3) :=
    ((Finset.measurable_sum _ fun i _ => hfm i).abs).pow_const _
  have hdom : Integrable (fun ω => (Fintype.card ι : ℝ)^2 * ∑ i, |f i ω| ^ 3) P :=
    (integrable_finsetSum _ fun i _ => hfi i).const_mul _
  refine hdom.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h₁ := pow_le_pow_left₀ (abs_nonneg (∑ i, f i ω)) (Finset.abs_sum_le_sum_abs _ _) 3
  have h₂ := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset ι))
    (f := fun i => |f i ω|) (fun i _ => abs_nonneg (f i ω)) 2
  exact h₁.trans (by simpa using h₂)
