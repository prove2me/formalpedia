-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.ConvergesAt.finite_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:55.272197+00:00
-- url     : https://prove2.me/submissions/db185345-85f5-42bc-882e-a5ac4b056401

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
namespace GroundTheory.PAdicHodge.Laurent
namespace ConvergesAt
theorem _root_.solution (h : ConvergesAt a ρ) {ε : ℝ} (hε : 0 < ε) :
    {n | ε ≤ ‖a n‖ * ρ ^ n}.Finite := by
  have := Filter.eventually_cofinite.1 (h.eventually (gt_mem_nhds hε))
  simpa only [not_lt] using this
end ConvergesAt
end GroundTheory.PAdicHodge.Laurent
