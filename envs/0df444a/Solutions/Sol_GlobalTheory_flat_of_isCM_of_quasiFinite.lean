-- Prove2me | solution 1 for GlobalTheory.flat_of_isCM_of_quasiFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:46:18.859919+00:00
-- url     : https://prove2.me/submissions/e843c24a-3a52-4c99-8d57-3bbde3374033

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Theorems.Thm_GlobalTheory_flat_of_isCM_of_ringKrullDim_add_le
import Theorems.Thm_GlobalTheory_ringKrullDim_quotient_map_maximalIdeal_le_zero

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
open ReciprocityTheory.CA
variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
namespace GlobalTheory
theorem _root_.solution [IsRegularLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.QuasiFinite A B] (hB : IsCM B)
    (hd : ringKrullDim A ≤ ringKrullDim B) : Module.Flat A B :=
  flat_of_isCM_of_ringKrullDim_add_le hB
    ((add_le_add_right ringKrullDim_quotient_map_maximalIdeal_le_zero _).trans (by rwa [add_zero]))
end GlobalTheory
