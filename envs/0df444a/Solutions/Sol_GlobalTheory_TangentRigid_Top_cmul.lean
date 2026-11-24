-- Prove2me | solution 1 for GlobalTheory.TangentRigid.Top.cmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:10:32.462801+00:00
-- url     : https://prove2.me/submissions/5d9ec4bc-7945-456b-9c4f-c482c4c71c80

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
theorem _root_.solution (a : k) (hp : Top p d c) : Top (C a * p) d (a * c) :=
  ⟨(natDegree_C_mul_le _ _).trans hp.1, by rw [coeff_C_mul, hp.2]⟩
end Top
end GlobalTheory.TangentRigid
