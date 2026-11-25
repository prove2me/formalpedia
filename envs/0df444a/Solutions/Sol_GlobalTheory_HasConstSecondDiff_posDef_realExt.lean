-- Prove2me | solution 1 for GlobalTheory.HasConstSecondDiff.posDef_realExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:48:45.672225+00:00
-- url     : https://prove2.me/submissions/1ed14dec-7ca5-45f4-9b49-4efb733ea8bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_posDef_realExt_of_tendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]
namespace GlobalTheory
namespace HasConstSecondDiff
theorem _root_.solution [Module.Finite ℤ X] {f : X → ℝ}
    (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) (ht : Tendsto f cofinite atTop) :
    (realExt (h.quadraticMap he)).PosDef :=
  posDef_realExt_of_tendsto _ (tendsto_atTop_add_const_right _ (-f 0) ht)
end HasConstSecondDiff
end GlobalTheory
