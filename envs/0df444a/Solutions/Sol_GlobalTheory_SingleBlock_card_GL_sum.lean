-- Prove2me | solution 1 for GlobalTheory.SingleBlock.card_GL_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:42.088629+00:00
-- url     : https://prove2.me/submissions/becc8ff1-036a-4c03-accc-5610682482d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.SingleBlock
variable {k : Type} [Field k] {r t : ℕ}
namespace GlobalTheory.SingleBlock
theorem _root_.solution : Nat.card (GL (Fin r ⊕ Fin t) k) = Nat.card (GL (Fin (r + t)) k) :=
  Nat.card_congr
    (Units.mapEquiv (Matrix.reindexAlgEquiv k k finSumFinEquiv).toRingEquiv.toMulEquiv).toEquiv
end GlobalTheory.SingleBlock
