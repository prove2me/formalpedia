-- Prove2me | solution 1 for GlobalTheory.flat_of_isCM_of_ringKrullDim_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:19.821339+00:00
-- url     : https://prove2.me/submissions/5c31f65e-7360-45cb-aa68-f30fded1a824

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Theorems.Thm_GlobalTheory_flat_of_isWeaklyRegular_of_isLocalHom

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
    [IsLocalHom (algebraMap A B)] (hB : IsCM B)
    (hd : ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) ≤
      ringKrullDim B) : Module.Flat A B := by
  have := hB.1
  obtain ⟨xs, h, hl⟩ := exists_ofList_eq_maximalIdeal_length_eq A
  refine flat_of_isWeaklyRegular_of_isLocalHom B h ?_
  rw [← isWeaklyRegular_map_algebraMap_iff B]
  refine (isRegular_of_isCM_of_ringKrullDim_quotient_add_length_le hB (fun y hy => ?_) ?_).1
  · refine map_maximalIdeal_le (algebraMap A B) ?_
    rw [← h, Ideal.map_ofList]
    exact Ideal.subset_span hy
  · rwa [← Ideal.map_ofList, h, List.length_map, hl, add_comm]
end GlobalTheory
