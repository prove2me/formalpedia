-- Prove2me | solution 1 for GlobalTheory.natCard_algHom_eq_finrank_of_isReduced_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:23:19.696257+00:00
-- url     : https://prove2.me/submissions/1eb9cd4a-8b8a-4cc4-813e-f11f1ed706a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin

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
variable (R S L : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field L] [Algebra R L]
namespace GlobalTheory
theorem _root_.solution [Module.Free R S] [Module.Finite R S]
    [IsAlgClosed L] [IsReduced (L ⊗[R] S)] : Nat.card (S →ₐ[R] L) = finrank R S :=
  have := etale_of_isReduced_of_perfectField L (L ⊗[R] S)
  natCard_algHom_eq_finrank_of_etale_baseChange R S L
end GlobalTheory
