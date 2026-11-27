-- Prove2me | solution 2 for GroundTheory.PAdicHodge.Laurent.highIndex_le_lowIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:17.573207+00:00
-- url     : https://prove2.me/submissions/ecc5c156-5dd7-40e0-a8ab-7e0d460f920c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_lowIndex_mem
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_highIndex_mem
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_le_of_mem_domSet

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
theorem _root_.solution {ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ') (h : ConvergesAt a ρ)
    (h' : ConvergesAt a ρ') (ha : a ≠ 0) : highIndex a ρ ≤ lowIndex a ρ' :=
  le_of_mem_domSet hρ hρρ' h h' ha (highIndex_mem hρ h ha)
    (lowIndex_mem (hρ.trans hρρ') h' ha)
end GroundTheory.PAdicHodge.Laurent
