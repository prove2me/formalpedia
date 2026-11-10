-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.conditionalRevenue_succ_expected_piecewise
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T16:36:23.301228+00:00
-- url     : https://prove2.me/submissions/7015eec9-3803-469d-960b-0bff1eb5cb3f

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option autoImplicit false

open NestedSeatAlloc.IntPolicy MeasureTheory ProbabilityTheory in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) (y s : ℝ),
    condRevenue P X f p (k + 1) y s =
      (if s < p k then expRevenue P X f p k s
       else if s < p k + y then (s - p k) * f (k + 1) + expRevenue P X f p k (p k)
       else y * f (k + 1) + expRevenue P X f p k (s - y))) := by
  intro h
  have h1 := h (0 : Measure Unit) (fun _ _ => (1 : ℝ)) (fun k => 3 - (k : ℝ))
    (fun _ => (0 : ℝ)) 1 le_rfl 1 1
  simp only [condRevenue, expRevenue, integral_zero_measure] at h1
  norm_num at h1
