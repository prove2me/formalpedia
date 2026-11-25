-- Prove2me | solution 1 for GlobalTheory.flat_of_isRegularLocalRing_of_quasiFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:05:24.652159+00:00
-- url     : https://prove2.me/submissions/9e61f099-0b75-4fec-adaf-63bb15f13e3e

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Theorems.Thm_GlobalTheory_flat_of_isCM_of_quasiFinite

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
theorem _root_.solution [IsRegularLocalRing A] [IsRegularLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.QuasiFinite A B]
    (hd : ringKrullDim A = ringKrullDim B) : Module.Flat A B :=
  flat_of_isCM_of_quasiFinite (isCM_of_isRegularLocalRing B) hd.le
end GlobalTheory
