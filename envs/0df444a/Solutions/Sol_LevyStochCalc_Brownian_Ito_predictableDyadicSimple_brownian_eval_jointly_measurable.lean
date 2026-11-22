-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_eval_jointly_measurable
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:41:39.384133+00:00
-- url     : https://prove2.me/submissions/7e22670c-e5bc-4a61-a144-33413858d2ef

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# `L²` convergence of the predictable dyadic approximations

For a bounded jointly measurable integrand the left-shifted dyadic simple processes
converge to it in `L²(Ω × [0,T])`, giving density of the simple predictable processes and
of the adapted simple processes in the bounded case, joint measurability of the evaluation
map and the `L²` Cauchy property of the approximating sequence.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]



theorem _root_.solution
    {T : ℝ} (hT : 0 < T) (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) :
    Measurable (fun (p : Ω × ℝ) =>
      (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
  classical
  let H := predictableDyadicSimple_brownian hT g h_meas M h_bound n
  change Measurable (fun p : Ω × ℝ => H.eval p.2 p.1)
  simp only [SimplePredictable.eval]
  refine Finset.measurable_sum _ fun i _ => ?_
  let S : Set (Ω × ℝ) := Prod.snd ⁻¹' Set.Ioc (H.partition i.castSucc) (H.partition i.succ)
  have hs : MeasurableSet S := measurable_snd measurableSet_Ioc
  have hm := ((H.ξ_measurable i).comp measurable_fst).indicator hs
  convert hm using 1
  funext p
  simp [S, Set.indicator_apply]
