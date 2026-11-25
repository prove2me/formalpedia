-- Prove2me | solution 1 for GlobalTheory.flat_of_isWeaklyRegular_of_isLocalHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:29:29.398248+00:00
-- url     : https://prove2.me/submissions/7e0e55f5-d997-4e4a-927d-4ab758f83b09

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Theorems.Thm_GlobalTheory_flat_of_isWeaklyRegular_of_le_jacobson

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
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    {xs : List A} (hxs : Ideal.ofList xs = maximalIdeal A) (h : IsWeaklyRegular M xs) :
    Module.Flat A M :=
  flat_of_isWeaklyRegular_of_le_jacobson B
    ((map_maximalIdeal_le _).trans (maximalIdeal_le_jacobson _)) hxs h
end GlobalTheory
