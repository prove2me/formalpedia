-- Prove2me | solution 2 for GroundTheory.PAdicHodge.Laurent.lowIndex_le_highIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:23.444855+00:00
-- url     : https://prove2.me/submissions/e7cef569-5809-4597-9ce2-cdf5ef0eb69c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_highIndex_mem
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_lowIndex_le

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
variable (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0)
include hρ h ha
namespace GroundTheory.PAdicHodge.Laurent
theorem _root_.solution : lowIndex a ρ ≤ highIndex a ρ :=
  lowIndex_le hρ h ha (highIndex_mem hρ h ha)
end GroundTheory.PAdicHodge.Laurent
