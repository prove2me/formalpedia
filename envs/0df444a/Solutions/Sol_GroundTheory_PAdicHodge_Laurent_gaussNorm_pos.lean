-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.gaussNorm_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:29.260273+00:00
-- url     : https://prove2.me/submissions/4ac1a5ce-b9e0-40e9-9199-716cb3d4a4e3

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_le_gaussNorm

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
theorem _root_.solution : 0 < gaussNorm a ρ := by
  obtain ⟨n0, hn0⟩ := Function.ne_iff.1 ha
  have := norm_pos_iff.2 hn0
  exact lt_of_lt_of_le (by positivity) (h.le_gaussNorm n0)
end GroundTheory.PAdicHodge.Laurent
