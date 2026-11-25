-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.ConvergesAt.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:34:25.155466+00:00
-- url     : https://prove2.me/submissions/a5446529-2a18-4169-9256-6d9ddee5e23b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_add
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_neg

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
namespace GroundTheory.PAdicHodge.Laurent
namespace ConvergesAt
theorem _root_.solution (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) :
    ConvergesAt (a - b) ρ := by
  simpa [sub_eq_add_neg] using ha.add hρ hb.neg
end ConvergesAt
end GroundTheory.PAdicHodge.Laurent
