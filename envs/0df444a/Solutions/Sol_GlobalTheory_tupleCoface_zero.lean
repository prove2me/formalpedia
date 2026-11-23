-- Prove2me | solution 1 for GlobalTheory.tupleCoface_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:45.144891+00:00
-- url     : https://prove2.me/submissions/1baf69f1-e19e-4967-b414-ee6cb26133ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finsupp
open GlobalTheory
variable {X : Type*}
namespace GlobalTheory
theorem _root_.solution (a b : X) {n : ℕ} (x : Fin n → X) :
    tupleCoface a b 0 x = Fin.cons a x := by
  funext j
  simp only [tupleCoface, Fin.zero_le, if_true]
  induction j using Fin.cases with
  | zero => simp
  | succ j => simp [← Fin.succ_castSucc]
end GlobalTheory
