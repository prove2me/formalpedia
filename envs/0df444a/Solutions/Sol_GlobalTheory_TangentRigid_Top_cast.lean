-- Prove2me | solution 1 for GlobalTheory.TangentRigid.Top.cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:10:31.834798+00:00
-- url     : https://prove2.me/submissions/9b3a7f77-8b6d-4968-8179-680041a9482a

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
namespace Top
theorem _root_.solution {p' : k[X]} (hp : Top p d c) (h0 : p = p') (h : d = e) (h' : c = c') :
    Top p' e c' := by
  subst h0 h h'; exact hp
end Top
end GlobalTheory.TangentRigid
