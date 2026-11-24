-- Prove2me | solution 1 for GlobalTheory.TangentRigid.Top.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:10:30.977+00:00
-- url     : https://prove2.me/submissions/f76fbdfb-7a74-4b68-b5e3-af08559f1d81

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
theorem _root_.solution (hp : Top p d c) (hq : Top q d c') : Top (p + q) d (c + c') :=
  ⟨(natDegree_add_le _ _).trans (max_le hp.1 hq.1), by rw [coeff_add, hp.2, hq.2]⟩
end Top
end GlobalTheory.TangentRigid
