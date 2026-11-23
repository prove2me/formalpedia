-- Prove2me | solution 1 for GlobalTheory.JetConj.JetRel.zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:04.20641+00:00
-- url     : https://prove2.me/submissions/bb099866-cf61-452d-9dc7-061eef9f4901

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
theorem _root_.solution (H : JetRel S f f') : (f 0, f' 0) ∈ S := by simpa using H.2.2 0
end JetRel
end GlobalTheory.JetConj
