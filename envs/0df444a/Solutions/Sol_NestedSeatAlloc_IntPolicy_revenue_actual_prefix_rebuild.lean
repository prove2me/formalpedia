-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.revenue_actual_prefix_rebuild
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:27:45.935509+00:00
-- url     : https://prove2.me/submissions/81c336da-7f87-41ab-99c4-efe31c2ea254

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_prefixRevenueRebuild
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_frozen_prefix_rebuild

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ)
    (ω : Ω) (s : ℝ) :
    revenue f p (fun i => X i ω) (k + 1) s =
    revenue f p (prefixRevenueRebuild k
      (X (k + 1) ω, fun i : (Finset.Icc 1 k) => X i.1 ω))
      (k + 1) s := by
  simpa only [Function.update_eq_self] using
    (revenue_frozen_prefix_rebuild X f p k ω (X (k + 1) ω) s)
