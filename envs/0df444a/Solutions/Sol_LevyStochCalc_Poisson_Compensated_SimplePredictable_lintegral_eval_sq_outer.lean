-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.SimplePredictable.lintegral_eval_sq_outer
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:56:21.910574+00:00
-- url     : https://prove2.me/submissions/043c6738-035a-4fcb-880e-9c9ae264ff4f

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Compensated Poisson integral: simple predictable integrands

The simple predictable integrands `φ = ∑_i ξ_i · 1_{(t_i, t_{i+1}] × A_i}` and
their integral `simpleIntegral` against the compensated Poisson measure
`Ñ(dt, de) := N(dt, de) − ν(de) dt`, with the indicator/rectangle bookkeeping
lemmas. The moment identities are in `Poisson/CompensatedMoments.lean`; the
L²-isometry in `Poisson/CompensatedIsometry.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]



theorem _root_.solution
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      = ∑ i : Fin φ.N,
        LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) *
        ∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  simp_rw [SimplePredictable.lintegral_eval_sq φ]
  rw [lintegral_finset_sum _ (fun i _ =>
    ((φ.ξ_measurable i).nnnorm.coe_nnreal_ennreal.pow_const 2).mul_const _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [lintegral_mul_const _ ((φ.ξ_measurable i).nnnorm.coe_nnreal_ennreal.pow_const 2), mul_comm]

