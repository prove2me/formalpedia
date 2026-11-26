-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.zero_cmul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T14:32:49.731025+00:00
-- url     : https://prove2.me/submissions/fa366457-21ea-422a-bf79-20d70c91b0df

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
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

theorem solution (a : ℤ → K) : cmul 0 a = 0 := by
  ext n
  simp [cmul, tsum_zero]
