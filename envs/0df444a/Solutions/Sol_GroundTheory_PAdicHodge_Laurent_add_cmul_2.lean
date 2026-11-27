-- Prove2me | solution 2 for GroundTheory.PAdicHodge.Laurent.add_cmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:49.823586+00:00
-- url     : https://prove2.me/submissions/b5486210-c0b8-4b01-8103-d07df16a73d7

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_comm
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_add

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
theorem _root_.solution (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (hc : ConvergesAt c ρ) : cmul (a + b) c = cmul a c + cmul b c := by
  rw [cmul_comm, cmul_add hρ hc ha hb, cmul_comm c, cmul_comm c]
end GroundTheory.PAdicHodge.Laurent
