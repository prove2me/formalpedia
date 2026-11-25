-- Prove2me | solution 1 for GlobalTheory.algebraMap_norm_eq_prod_of_equiv_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:54:20.774585+00:00
-- url     : https://prove2.me/submissions/19a3c20d-6501-4d83-87a0-4c4850c2d3ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_algebraMap_norm_eq_prod_algHom_of_card
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
theorem _root_.solution (P : ι ≃ (S →ₐ[K] L)) (x : S) :
    algebraMap K L (Algebra.norm K x) = ∏ j, P j x :=
  have := Algebra.FormallyUnramified.finite_of_free K S
  algebraMap_norm_eq_prod_algHom_of_card (card_eq_finrank_of_equiv_algHom P) P.injective x
end GlobalTheory
