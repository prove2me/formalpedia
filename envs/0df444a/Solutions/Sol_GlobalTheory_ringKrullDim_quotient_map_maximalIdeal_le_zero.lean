-- Prove2me | solution 1 for GlobalTheory.ringKrullDim_quotient_map_maximalIdeal_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:55.867384+00:00
-- url     : https://prove2.me/submissions/0fe4d898-8e8a-4a7c-9756-3550bed35379

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
open ReciprocityTheory.CA
variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
namespace GlobalTheory
theorem _root_.solution [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.QuasiFinite A B] :
    ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) ≤ 0 := by
  refine ringKrullDim_quotient_le_zero_of_forall_eq fun p hp hle => ?_
  refine Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) _ _ (le_maximalIdeal hp.ne_top) ?_
  exact ((maximalIdeal.isMaximal A).eq_of_le (Ideal.comap_ne_top _ hp.ne_top)
    (Ideal.map_le_iff_le_comap.mp hle)).symm.trans (maximalIdeal_comap _).symm
end GlobalTheory
