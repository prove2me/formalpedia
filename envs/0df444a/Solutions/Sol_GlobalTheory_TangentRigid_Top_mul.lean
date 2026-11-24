-- Prove2me | solution 1 for GlobalTheory.TangentRigid.Top.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:10:33.398203+00:00
-- url     : https://prove2.me/submissions/6dd78c52-cd41-4be1-b681-807051df60da

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
theorem _root_.solution (hp : Top p d c) (hq : Top q e c') : Top (p * q) (d + e) (c * c') :=
  ⟨natDegree_mul_le.trans (add_le_add hp.1 hq.1), by
    rw [coeff_mul_add_eq_of_natDegree_le hp.1 hq.1, hp.2, hq.2]⟩
end Top
end GlobalTheory.TangentRigid
