-- Prove2me | solution 1 for GlobalTheory.isRegular_of_length_eq_spanFinrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:35.664517+00:00
-- url     : https://prove2.me/submissions/345b8e11-7531-4198-b885-ddf48b683496

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open RingTheory.Sequence IsLocalRing TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R]
universe u
namespace GlobalTheory
theorem _root_.solution [IsRegularLocalRing R] {xs : List R}
    (h : Ideal.ofList xs = maximalIdeal R) (hd : xs.length = (maximalIdeal R).spanFinrank) :
    RingTheory.Sequence.IsRegular R xs :=
  isRegular_of_ofList_eq_maximalIdeal h (by rw [hd, IsRegularLocalRing.spanFinrank_maximalIdeal])
end GlobalTheory
