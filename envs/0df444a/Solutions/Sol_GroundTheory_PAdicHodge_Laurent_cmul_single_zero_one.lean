-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.cmul_single_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:20.698269+00:00
-- url     : https://prove2.me/submissions/e1e09a4c-e14f-44aa-a0b6-4cc9f4e75453

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
namespace GroundTheory.PAdicHodge.Laurent
theorem _root_.solution (a : ℤ → K) : cmul a (Pi.single 0 1) = a := by
  funext n
  unfold cmul
  rw [tsum_eq_single n fun i hi => by simp [Pi.single_apply, sub_eq_zero, Ne.symm hi]]
  simp
end GroundTheory.PAdicHodge.Laurent
