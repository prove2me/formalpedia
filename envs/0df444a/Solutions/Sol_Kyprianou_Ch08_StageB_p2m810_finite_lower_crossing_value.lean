-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_finite_lower_crossing_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:33:44.624227+00:00
-- url     : https://prove2.me/submissions/dc532014-fae0-4a6b-b58d-18b06b580522

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_finite_upper_crossing_value
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Order.TypeTags
import Mathlib.Topology.Defs.Filter
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
      (l : ℝ) (u : ℝ≥0),
      ContinuousWithinAt (fun t => X t ω) (Ici u) u →
      tauMinus X l ω = (u : WithTop ℝ≥0) → X u ω ≤ l := by
  intro Ω X ω l u hc ht
  have he : tauPlus (fun t ω => -X t ω) (-l) ω = tauMinus X l ω := by
    unfold tauPlus tauMinus
    congr 1
    ext t
    simp only [mem_setOf_eq, neg_lt_neg_iff]
  exact neg_le_neg_iff.mp
    (p2m810_finite_upper_crossing_value Ω (fun t ω => -X t ω) ω (-l) u hc.neg
      (he.trans ht))
