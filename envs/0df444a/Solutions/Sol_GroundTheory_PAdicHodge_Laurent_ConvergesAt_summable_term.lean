-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.ConvergesAt.summable_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:16:26.186204+00:00
-- url     : https://prove2.me/submissions/ef54d846-a5f7-4b4c-b157-4429585900d9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_tendsto_term

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
theorem _root_.solution [CompleteSpace K] (hρ : 0 < ρ) (ha : ConvergesAt a ρ)
    (hb : ConvergesAt b ρ) (n : ℤ) : Summable (fun i => a i * b (n - i)) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (ha.tendsto_term hρ hb n)
end ConvergesAt
end GroundTheory.PAdicHodge.Laurent
