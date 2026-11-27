-- Prove2me | solution 2 for GroundTheory.PAdicHodge.Laurent.ConvergesAt.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:44.721517+00:00
-- url     : https://prove2.me/submissions/9fdb0a9f-e7b5-4226-88b1-9bdefd78c936

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
theorem _root_.solution (k : K) (ha : ConvergesAt a ρ) : ConvergesAt (k • a) ρ := by
  simpa [ConvergesAt, norm_mul, mul_assoc] using ha.const_mul ‖k‖
end ConvergesAt
end GroundTheory.PAdicHodge.Laurent
