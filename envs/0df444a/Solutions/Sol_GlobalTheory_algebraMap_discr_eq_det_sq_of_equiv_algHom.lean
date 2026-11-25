-- Prove2me | solution 1 for GlobalTheory.algebraMap_discr_eq_det_sq_of_equiv_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:32:47.638271+00:00
-- url     : https://prove2.me/submissions/db7c70d3-4d5c-4d2b-863b-dfd2a741f95b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_algebraMap_discr_eq_det_sq_of_card
import Theorems.Thm_GlobalTheory_card_eq_finrank_of_equiv_algHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable (K : Type*) {S : Type*} (L : Type*) [Field K] [CommRing S] [Algebra K S] [Field L]
  [Algebra K L] [IsSepClosed L] [Algebra.Etale K S]
variable {K L} {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution [DecidableEq ι] (P : ι ≃ (S →ₐ[K] L))
    (v : ι → S) :
    algebraMap K L (Algebra.discr K v) = (Matrix.of fun i j => P j (v i)).det ^ 2 :=
  have := Algebra.FormallyUnramified.finite_of_free K S
  algebraMap_discr_eq_det_sq_of_card (card_eq_finrank_of_equiv_algHom P) P.injective v
end GlobalTheory
