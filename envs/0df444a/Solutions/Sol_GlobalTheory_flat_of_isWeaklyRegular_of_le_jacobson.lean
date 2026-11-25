-- Prove2me | solution 1 for GlobalTheory.flat_of_isWeaklyRegular_of_le_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:23.565091+00:00
-- url     : https://prove2.me/submissions/8f55abbe-9daa-458e-853b-5cf4350a10ad

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_flat_of_isMaximal
import Theorems.Thm_GlobalTheory_isQuasiRegularSeq_get_of_isWeaklyRegular


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
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution [IsNoetherianRing A] [IsLocalRing A] (B : Type*)
    [CommRing B] [IsNoetherianRing B] [Algebra A B] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] (hB : (maximalIdeal A).map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson)
    {xs : List A} (hxs : Ideal.ofList xs = maximalIdeal A) (h : IsWeaklyRegular M xs) :
    Module.Flat A M := by
  have he : Ideal.span (Set.range xs.get) = maximalIdeal A := by
    rw [← ofList_ofFn_eq_span_range, List.ofFn_get, hxs]
  refine (isQuasiRegularSeq_get_of_isWeaklyRegular h).flat_of_isMaximal B ?_ ?_ <;> rw [he]
  exacts [inferInstance, hB]
end GlobalTheory
