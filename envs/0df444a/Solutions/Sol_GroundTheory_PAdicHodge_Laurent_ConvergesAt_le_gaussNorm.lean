-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.ConvergesAt.le_gaussNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:41.29457+00:00
-- url     : https://prove2.me/submissions/fedaaaaa-caa1-4d84-8ad4-a39ca34f1150

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_bddAbove

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
theorem _root_.solution (h : ConvergesAt a ρ) (n : ℤ) :
    ‖a n‖ * ρ ^ n ≤ gaussNorm a ρ :=
  le_ciSup h.bddAbove n
end ConvergesAt
end GroundTheory.PAdicHodge.Laurent
