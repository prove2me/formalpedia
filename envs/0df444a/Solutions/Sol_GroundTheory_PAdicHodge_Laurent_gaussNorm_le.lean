-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.gaussNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:43.896206+00:00
-- url     : https://prove2.me/submissions/23d09456-61bf-451e-8d74-f50f2c9e7941

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
theorem _root_.solution {C : ℝ} (h : ∀ n, ‖a n‖ * ρ ^ n ≤ C) : gaussNorm a ρ ≤ C :=
  ciSup_le h
end GroundTheory.PAdicHodge.Laurent
