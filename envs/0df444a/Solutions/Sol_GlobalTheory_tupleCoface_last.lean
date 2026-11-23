-- Prove2me | solution 1 for GlobalTheory.tupleCoface_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:29.222909+00:00
-- url     : https://prove2.me/submissions/662f8d46-2181-468a-bd68-3e326b746f17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential
import Theorems.Thm_GlobalTheory_tupleCoface_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.tupleCoface_zero

set_option autoImplicit false
open Finsupp
open GlobalTheory
variable {X : Type*}
namespace GlobalTheory
theorem _root_.solution (a b : X) {n : ℕ} (x : Fin n → X) :
    tupleCoface a b (Fin.last (n + 1)) x = Fin.snoc x b := by
  funext j
  simp [tupleCoface, (Fin.castSucc_lt_last j).not_ge]
end GlobalTheory
