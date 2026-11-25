-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.cmul_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:34.456261+00:00
-- url     : https://prove2.me/submissions/c14361fc-0c2a-4d3c-8270-5442cf783cea

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_summable_term

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
theorem _root_.solution (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (hc : ConvergesAt c ρ) : cmul a (b + c) = cmul a b + cmul a c := by
  funext n
  simp only [cmul, Pi.add_apply, mul_add]
  exact (ha.summable_term hρ hb n).tsum_add (ha.summable_term hρ hc n)
end GroundTheory.PAdicHodge.Laurent
