-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.ne_zero_of_mem_domSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:39.709834+00:00
-- url     : https://prove2.me/submissions/50d48d57-c62a-4f25-a957-54ae88b6c116

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_pos

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
theorem _root_.solution {n : ℤ} (hn : n ∈ domSet a ρ) : a n ≠ 0 := by
  intro h0
  have := gaussNorm_pos hρ h ha
  simp only [domSet, Set.mem_setOf_eq, h0, norm_zero, zero_mul] at hn
  linarith
end GroundTheory.PAdicHodge.Laurent
