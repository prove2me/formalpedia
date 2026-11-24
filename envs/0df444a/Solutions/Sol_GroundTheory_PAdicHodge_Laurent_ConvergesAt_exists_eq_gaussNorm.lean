-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.ConvergesAt.exists_eq_gaussNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:52:54.303854+00:00
-- url     : https://prove2.me/submissions/5389db48-1c2e-4f45-950d-0d0159f31e8d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_le_gaussNorm
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_le
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_finite_le

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
namespace ConvergesAt
theorem _root_.solution : ∃ n, ‖a n‖ * ρ ^ n = gaussNorm a ρ := by
  obtain ⟨n0, hn0⟩ := Function.ne_iff.1 ha
  have hε : 0 < ‖a n0‖ * ρ ^ n0 := by have := norm_pos_iff.2 hn0; positivity
  set S := (h.finite_le hε).toFinset
  have hn0S : n0 ∈ S := by simp [S]
  obtain ⟨m, hmS, hm⟩ := S.exists_max_image (fun n => ‖a n‖ * ρ ^ n) ⟨n0, hn0S⟩
  refine ⟨m, le_antisymm (h.le_gaussNorm m) (gaussNorm_le fun n => ?_)⟩
  by_cases hn : n ∈ S
  · exact hm n hn
  · simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hn
    exact hn.le.trans (hm n0 hn0S)
end ConvergesAt
end GroundTheory.PAdicHodge.Laurent
