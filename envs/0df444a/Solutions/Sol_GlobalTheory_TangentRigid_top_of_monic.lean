-- Prove2me | solution 1 for GlobalTheory.TangentRigid.top_of_monic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:10:31.541358+00:00
-- url     : https://prove2.me/submissions/9e00cabb-336a-4158-b0f2-3a54b7631be6

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
theorem _root_.solution (hp : p.Monic) (h : p.natDegree = d) : Top p d 1 :=
  ⟨h.le, by rw [← h]; exact hp⟩
end GlobalTheory.TangentRigid
