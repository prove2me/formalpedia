-- Prove2me | solution 1 for GlobalTheory.TangentRigid.Top.raise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:10:26.483101+00:00
-- url     : https://prove2.me/submissions/cd6e9dd4-3e94-4d30-b202-65206882a48e

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
theorem _root_.solution (hp : Top p d c) (h : d < e) : Top p e 0 :=
  ⟨hp.1.trans h.le, coeff_eq_zero_of_natDegree_lt (hp.1.trans_lt h)⟩
end Top
end GlobalTheory.TangentRigid
