-- Prove2me | solution 1 for GlobalTheory.free_of_isRegularLocalRing_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:39:44.255727+00:00
-- url     : https://prove2.me/submissions/21d9ba57-d5ee-4ee9-a76c-65464108dbc6

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Theorems.Thm_GlobalTheory_flat_of_isRegularLocalRing_of_quasiFinite

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
    [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    (hd : ringKrullDim A = ringKrullDim B) : Module.Free A B :=
  have := flat_of_isRegularLocalRing_of_quasiFinite hd
  Module.free_of_flat_of_isLocalRing
end GlobalTheory
