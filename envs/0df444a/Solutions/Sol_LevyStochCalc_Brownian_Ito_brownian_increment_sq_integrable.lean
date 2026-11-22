-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.brownian_increment_sq_integrable
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:51:39.710649+00:00
-- url     : https://prove2.me/submissions/69eb9ce5-d78e-49b3-85c1-08367012d682

import Theorems.Thm_LevyStochCalc_Brownian_Martingale_brownianMotion_memLp_2
import Definitions.Def_LevyStochCalc_Brownian_Filtered_F001
import Definitions.Def_LevyStochCalc_Brownian_Filtered_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second moments of the terms of the elementary Brownian integral

For an adapted simple predictable integrand the diagonal term satisfies
`E[(ξ_i · ΔW_i) ^ 2] = (t_{i+1} - t_i) · E[ξ_i ^ 2]`, where
`ΔW_i = W_{t_{i+1}} - W_{t_i}`, since `ΔW_i` is independent of `ℱ_{t_i}` and centred Gaussian
with variance `t_{i+1} - t_i`, while for `i < j` the off-diagonal term vanishes,
`E[(ξ_i · ΔW_i) · (ξ_j · ΔW_j)] = 0`. Both rest on the integrability of the squared increments
and of the cross products.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]



theorem _root_.solution
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {s t : ℝ} (h_s_nn : 0 ≤ s) (h_st : s < t) :
    MeasureTheory.Integrable (fun ω => (W.W t ω - W.W s ω)^2) P := by
  have h : MemLp (fun ω => W.W t ω - W.W s ω) 2 P :=
    (LevyStochCalc.Brownian.Martingale.brownianMotion_memLp_2 W t).sub
      (LevyStochCalc.Brownian.Martingale.brownianMotion_memLp_2 W s)
  refine (h.integrable_mul h).congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [pow_two]
