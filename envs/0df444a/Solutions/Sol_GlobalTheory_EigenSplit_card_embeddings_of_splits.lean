-- Prove2me | solution 1 for GlobalTheory.EigenSplit.card_embeddings_of_splits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:24:59.424194+00:00
-- url     : https://prove2.me/submissions/2be15165-0274-4858-b054-8c9c9d398fa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.EigenSplit
theorem _root_.solution {L : Type*} [Field L] [CharZero L] [Fintype (E →+* L)]
    (hL : ∀ x : E, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits) :
    Fintype.card (E →+* L) = Module.finrank ℚ E := by
  rw [← AlgHom.card_of_splits ℚ E L hL]
  exact Fintype.card_congr (RingHom.equivRatAlgHom _ _)
end GlobalTheory.EigenSplit
