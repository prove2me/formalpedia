-- Prove2me | solution 2 for GroundTheory.PAdicHodge.Laurent.single_zero_one_cmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:25.930828+00:00
-- url     : https://prove2.me/submissions/58f2e298-340c-482d-9b41-a8f6d16f7a1a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_comm
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_single_zero_one

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
variable [CompleteSpace K]
namespace GroundTheory.PAdicHodge.Laurent
theorem _root_.solution (a : ℤ → K) : cmul (Pi.single 0 1) a = a := by
  rw [cmul_comm, cmul_single_zero_one]
end GroundTheory.PAdicHodge.Laurent
