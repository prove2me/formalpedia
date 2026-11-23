-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.ConvergesAt.bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:01.204424+00:00
-- url     : https://prove2.me/submissions/0531e05d-78bd-4ddb-9a94-aa57dc7dda7c

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
theorem _root_.solution (h : ConvergesAt a ρ) :
    BddAbove (Set.range fun n : ℤ => ‖a n‖ * ρ ^ n) :=
  h.bddAbove_range_of_cofinite
end ConvergesAt
end GroundTheory.PAdicHodge.Laurent
