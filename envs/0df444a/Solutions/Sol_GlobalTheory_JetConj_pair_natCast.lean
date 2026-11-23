-- Prove2me | solution 1 for GlobalTheory.JetConj.pair_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:28.473783+00:00
-- url     : https://prove2.me/submissions/ceb1ec3a-2757-4f5d-ac71-33d30b62477d

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
theorem _root_.solution (S : Subring (ℂ × ℂ)) (n : ℕ) : ((n : ℂ), (n : ℂ)) ∈ S := by
  convert natCast_mem S n using 1
  ext <;> simp
end GlobalTheory.JetConj
