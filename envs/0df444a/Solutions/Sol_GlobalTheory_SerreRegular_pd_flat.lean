-- Prove2me | solution 1 for GlobalTheory.SerreRegular.pd_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:19:00.635336+00:00
-- url     : https://prove2.me/submissions/3084d5b6-cb4a-48c2-93d8-0cb0bf6922be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Theorems.Thm_GlobalTheory_SerreRegular_pd_baseChange

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
open GlobalTheory.SerreRegular
namespace GlobalTheory.SerreRegular
theorem _root_.solution {A B : Type} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (n : ℕ) (M : ModuleCat.{0} A) [Module.Finite A M]
    (h : HasProjectiveDimensionLE M n) : HasProjectiveDimensionLE (ModuleCat.of B (B ⊗[A] M)) n :=
  pd_baseChange (fun _ => True) (fun _ _ f _ _ =>
    ⟨trivial, Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)⟩)
    n M trivial h
end GlobalTheory.SerreRegular
