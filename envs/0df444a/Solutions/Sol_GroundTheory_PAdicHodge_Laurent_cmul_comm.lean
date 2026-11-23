-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.cmul_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:38.572894+00:00
-- url     : https://prove2.me/submissions/06cb49a4-783d-4e06-bc52-260c07301fff

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
theorem _root_.solution (a b : ℤ → K) : cmul a b = cmul b a := by
  funext n
  unfold cmul
  rw [← (Equiv.subLeft n).tsum_eq (fun i => a i * b (n - i))]
  simp [Equiv.subLeft_apply, mul_comm]
end GroundTheory.PAdicHodge.Laurent
