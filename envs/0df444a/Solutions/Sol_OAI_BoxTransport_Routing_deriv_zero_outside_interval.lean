-- Prove2me | solution 1 for OAI.BoxTransport.Routing.deriv_zero_outside_interval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:34:57.793592+00:00
-- url     : https://prove2.me/submissions/57043b25-5cc8-4f75-9449-75e6390fb1c6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Flow.lean:L664-L678
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.deriv_zero_outside_interval. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow

-- ---- from OAI.Analysis.BoxTransport.Flow ----
namespace OAI

/-! Localized solenoidal moving fields and their unique global flows. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
theorem deriv_zero_outside_interval {f : ℝ → Space} {a b : Space} {u v t : ℝ}
    (hbefore : ∀ s, s ≤ u → f s = a) (hafter : ∀ s, v ≤ s → f s = b)
    (ht : t ∉ Set.Icc u v) : deriv f t = 0 := by
  by_cases hlo : t < u
  · have he : f =ᶠ[nhds t] fun _ => a := by
      filter_upwards [eventually_lt_nhds hlo] with s hs
      exact hbefore s hs.le
    simp [deriv, he.fderiv_eq]
  · have hhi : v < t := by
      by_contra hh
      exact ht ⟨le_of_not_gt hlo, le_of_not_gt hh⟩
    have he : f =ᶠ[nhds t] fun _ => b := by
      filter_upwards [eventually_gt_nhds hhi] with s hs
      exact hafter s hs.le
    simp [deriv, he.fderiv_eq]

end BoxTransport.Routing

end

end OAI

-- ---- platform node ----
open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.deriv_zero_outside_interval := @_root_.OAI.BoxTransport.Routing.deriv_zero_outside_interval
