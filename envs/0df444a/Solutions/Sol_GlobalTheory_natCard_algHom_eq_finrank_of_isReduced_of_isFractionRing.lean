-- Prove2me | solution 1 for GlobalTheory.natCard_algHom_eq_finrank_of_isReduced_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:34.455938+00:00
-- url     : https://prove2.me/submissions/61db8480-2ab8-4ff9-9fda-3c508e8b9dec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_natCard_algHom_eq_finrank_of_etale_tower

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
theorem _root_.solution [Module.Free R S]
    [Module.Finite R S] [IsReduced S] (K : Type*) [Field K] [PerfectField K] [Algebra R K]
    [IsFractionRing R K] [Algebra K L] [IsScalarTower R K L] [IsSepClosed L] :
    Nat.card (S →ₐ[R] L) = finrank R S := by
  have : IsReduced (K ⊗[R] S) := by
    letI : Algebra S (K ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    haveI := IsLocalization.tensorRight (S := S) K (nonZeroDivisors R)
    exact isReduced_of_injective (IsLocalization.algEquiv
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) (K ⊗[R] S)
      (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))))
      (AlgEquiv.injective _)
  have := etale_of_isReduced_of_perfectField K (K ⊗[R] S)
  exact natCard_algHom_eq_finrank_of_etale_tower R S L K
end GlobalTheory
