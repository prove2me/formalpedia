-- Prove2me | solution 2 for GroundTheory.PAdicHodge.Laurent.smul_cmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:30.761922+00:00
-- url     : https://prove2.me/submissions/e67d72d9-ca49-4e3c-920e-7aaaec411347

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_comm
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_smul

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
theorem _root_.solution (k : K) (a b : ℤ → K) : cmul (k • a) b = k • cmul a b := by
  rw [cmul_comm, cmul_smul, cmul_comm]
end GroundTheory.PAdicHodge.Laurent
