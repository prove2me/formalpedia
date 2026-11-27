-- Prove2me | solution 1 for GlobalTheory.flat_of_isRegularRing_of_isRegularRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:47.114814+00:00
-- url     : https://prove2.me/submissions/487e8555-8fc7-4058-8101-f609de94c952

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Theorems.Thm_GlobalTheory_flat_of_isRegularRing_of_isCM

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
theorem _root_.solution [IsRegularRing A] [IsRegularRing B]
    [Algebra.QuasiFinite A B]
    (hd : ∀ q : Ideal B, q.IsMaximal → (q.under A).height ≤ q.height) : Module.Flat A B :=
  flat_of_isRegularRing_of_isCM (fun _ _ => isCM_of_isRegularLocalRing _) hd
end GlobalTheory
