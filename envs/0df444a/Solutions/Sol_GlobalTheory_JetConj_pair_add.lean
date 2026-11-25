-- Prove2me | solution 1 for GlobalTheory.JetConj.pair_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:40.293299+00:00
-- url     : https://prove2.me/submissions/b8119a2d-85ab-4e9c-88c3-b921db73b4ed

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
theorem _root_.solution {a b c d : ℂ} (h1 : (a, b) ∈ S) (h2 : (c, d) ∈ S) : (a + c, b + d) ∈ S := S.add_mem h1 h2
end GlobalTheory.JetConj
