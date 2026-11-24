-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.highIndex_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:26:55.662428+00:00
-- url     : https://prove2.me/submissions/f56dee5c-e7be-463e-a8e3-497984a22d9d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_bddAbove
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_domSet_finite
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_domSet_nonempty

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
theorem _root_.solution : highIndex a ρ ∈ domSet a ρ :=
  Int.csSup_mem (domSet_nonempty hρ h ha) (domSet_finite hρ h ha).bddAbove
end GroundTheory.PAdicHodge.Laurent
