-- Prove2me | solution 1 for GlobalTheory.flat_of_isRegularRing_of_isCM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:22:28.015678+00:00
-- url     : https://prove2.me/submissions/9ae21049-e8f4-49a6-8791-3a67b0cb4b47

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Theorems.Thm_GlobalTheory_flat_localization_atPrime_of_isCM

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
theorem _root_.solution [IsRegularRing A] [Algebra.QuasiFinite A B]
    (hB : ∀ (q : Ideal B) [q.IsMaximal], IsCM (Localization.AtPrime q))
    (hd : ∀ q : Ideal B, q.IsMaximal → (q.under A).height ≤ q.height) : Module.Flat A B :=
  Module.flat_of_isLocalized_maximal B B (fun q _ => Localization.AtPrime q)
    (fun q _ => Algebra.linearMap B (Localization.AtPrime q))
    fun q hq => flat_localization_atPrime_of_isCM (q.under A) q (hB q) (hd q hq)
end GlobalTheory
