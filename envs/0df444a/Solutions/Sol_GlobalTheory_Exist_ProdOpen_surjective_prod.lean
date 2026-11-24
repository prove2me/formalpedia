-- Prove2me | solution 1 for GlobalTheory.Exist.ProdOpen.surjective_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:44:28.638425+00:00
-- url     : https://prove2.me/submissions/78ca09bb-4f3e-4d92-8c06-8049200a2c21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TrivProdOfSmallExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LineBundleTrivialBasicOpenOfTrivialFibreProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.AbLaw.CubeOpen
noncomputable section
open GlobalTheory GlobalTheory.Exist GlobalTheory.Exist.ProdOpen
namespace GlobalTheory.Exist.ProdOpen
theorem _root_.solution {S : Scheme.{0}} (X Y : Over S) (x₀ : 𝟙_ (Over S) ⟶ X)
    (y₀ : 𝟙_ (Over S) ⟶ Y) : Surjective (X ⊗ Y).hom := by
  have hw : (lift x₀ y₀).left ≫ (X ⊗ Y).hom = 𝟙 S := Over.w (lift x₀ y₀)
  refine ⟨fun s => ⟨(lift x₀ y₀).left s, ?_⟩⟩
  rw [← Scheme.Hom.comp_apply, hw]
  rfl
end GlobalTheory.Exist.ProdOpen
