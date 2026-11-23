-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.weight_lt_of_lt_lowIndex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:03.706664+00:00
-- url     : https://prove2.me/submissions/f6681a09-e274-49a1-9a40-174900b28a7c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_le_gaussNorm
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
theorem _root_.solution {n : ℤ} (hn : n < lowIndex a ρ) :
    ‖a n‖ * ρ ^ n < gaussNorm a ρ :=
  lt_of_le_of_ne (h.le_gaussNorm n) fun heq => absurd (lowIndex_le hρ h ha heq) (not_le.2 hn)
end GroundTheory.PAdicHodge.Laurent
