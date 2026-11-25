-- Prove2me | solution 1 for GlobalTheory.natCard_algHom_eq_finrank_of_etale_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:59.047589+00:00
-- url     : https://prove2.me/submissions/fdf99dbe-baac-455c-873b-6bf55256e9e1

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
    (K : Type*) [Field K] [Algebra R K] [Algebra K L] [IsScalarTower R K L] [IsSepClosed L]
    [Algebra.FormallyEtale K (K ⊗[R] S)] : Nat.card (S →ₐ[R] L) = finrank R S :=
  have : Algebra.FormallyEtale L (L ⊗[R] S) :=
    .of_equiv (Algebra.TensorProduct.cancelBaseChange R K L L S)
  natCard_algHom_eq_finrank_of_etale_baseChange R S L
end GlobalTheory
