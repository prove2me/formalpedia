-- Prove2me | solution 1 for GlobalTheory.TangentRigid.top_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:10:29.858525+00:00
-- url     : https://prove2.me/submissions/3bbc8f24-666d-491d-a4fa-8ea00ed32f77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FirstOrderRigid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TangentRigid
variable {k : Type} [Field k] {p q : k[X]} {d e : ℕ} {c c' : k}
namespace GlobalTheory.TangentRigid
theorem _root_.solution : Top (X : k[X]) 1 1 := ⟨natDegree_X_le, by simp⟩
end GlobalTheory.TangentRigid
