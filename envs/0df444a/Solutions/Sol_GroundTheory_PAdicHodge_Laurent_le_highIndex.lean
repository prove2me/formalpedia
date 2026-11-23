-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.le_highIndex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:26.322514+00:00
-- url     : https://prove2.me/submissions/ccc5a8c5-b213-494f-9d6e-e43ad2326f8f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_bddAbove
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_domSet_finite

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
theorem _root_.solution {n : ℤ} (hn : n ∈ domSet a ρ) : n ≤ highIndex a ρ :=
  le_csSup (domSet_finite hρ h ha).bddAbove hn
end GroundTheory.PAdicHodge.Laurent
