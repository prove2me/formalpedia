-- Prove2me | solution 1 for GlobalTheory.JetConj.pair_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:29.543821+00:00
-- url     : https://prove2.me/submissions/63e5783c-6905-4179-8578-a7d7e87e10ab

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
theorem _root_.solution {a b c d : ℂ} (h1 : (a, b) ∈ S) (h2 : (c, d) ∈ S) : (a - c, b - d) ∈ S := S.sub_mem h1 h2
end GlobalTheory.JetConj
