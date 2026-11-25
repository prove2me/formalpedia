-- Prove2me | solution 1 for GlobalTheory.isRegularLocalRing_of_hasProjectiveDimensionLE_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:43:49.137632+00:00
-- url     : https://prove2.me/submissions/272ff784-4445-4b44-894d-9377cee40449

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Theorems.Thm_GlobalTheory_SerreRegular_regular_of_pd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat CategoryTheory TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (A : Type) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (n : ℕ)
    (h : HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ maximalIdeal A)) n) :
    IsRegularLocalRing A :=
  SerreRegular.regular_of_pd _ A rfl ⟨n, h⟩
end GlobalTheory
