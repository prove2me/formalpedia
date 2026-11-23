-- Prove2me | solution 1 for GlobalTheory.JetConj.JetRel.const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:04.298247+00:00
-- url     : https://prove2.me/submissions/c15a3508-59ca-4800-8008-03dc435f02a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.JetConj
variable {S : Subring (ℂ × ℂ)} {f f' g g' h h' : ℂ → ℂ}
namespace GlobalTheory.JetConj
namespace JetRel
theorem _root_.solution {a b : ℂ} (h : (a, b) ∈ S) : JetRel S (fun _ => a) (fun _ => b) := by
  refine ⟨analyticAt_const, analyticAt_const, fun n => ?_⟩
  rw [iteratedDeriv_const, iteratedDeriv_const]
  split_ifs
  · exact h
  · exact S.zero_mem
end JetRel
end GlobalTheory.JetConj
