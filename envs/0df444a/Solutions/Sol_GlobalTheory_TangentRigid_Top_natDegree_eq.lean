-- Prove2me | solution 1 for GlobalTheory.TangentRigid.Top.natDegree_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:10:34.336408+00:00
-- url     : https://prove2.me/submissions/32d1460f-b212-46a9-8b0a-f86e5e434dbd

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
theorem _root_.solution (hp : Top p d 1) : p.natDegree = d :=
  le_antisymm hp.1 (le_natDegree_of_ne_zero (by rw [hp.2]; exact one_ne_zero))
end Top
end GlobalTheory.TangentRigid
