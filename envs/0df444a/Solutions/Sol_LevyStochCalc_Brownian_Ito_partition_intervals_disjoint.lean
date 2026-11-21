-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.partition_intervals_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T02:34:50.146635+00:00
-- url     : https://prove2.me/submissions/4e88a9f9-0867-4fdb-995f-8c287d419424

import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple predictable integrands and the elementary Brownian integral

The class `SimplePredictable` of integrands `∑_i ξ_i · 1_{(t_i, t_{i+1}]}` with bounded
measurable coefficients, their pointwise evaluation `SimplePredictable.eval`, the elementary
integral `simpleIntegral` against a scalar Brownian motion `W`, and the energy
`∫⁻ ‖H.eval s ω‖₊ ^ 2` of the integrand, which the disjointness of the partition intervals
`(t_i, t_{i+1}]` turns into the sum `∑_i (t_{i+1} - t_i) · ∫⁻ ‖ξ_i‖₊ ^ 2 ∂P`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]



theorem _root_.solution {T : ℝ} (H : SimplePredictable Ω T) :
    Pairwise (fun i j : Fin H.N => Disjoint
      (Set.Ioc (H.partition i.castSucc) (H.partition i.succ))
      (Set.Ioc (H.partition j.castSucc) (H.partition j.succ))) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hidx : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact Nat.succ_le_of_lt hlt
    exact (not_lt_of_ge (hi.2.trans (H.partition_strictMono.monotone hidx))) hj.1
  · have hidx : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      exact Nat.succ_le_of_lt hgt
    exact (not_lt_of_ge (hj.2.trans (H.partition_strictMono.monotone hidx))) hi.1
