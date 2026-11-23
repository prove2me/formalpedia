-- Prove2me | solution 1 for GlobalTheory.Exist.ProdOpen.isPullback_prodMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:54.309112+00:00
-- url     : https://prove2.me/submissions/ed100390-b560-4b43-a3d0-177538586460

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TrivProdOfSmallExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LineBundleTrivialBasicOpenOfTrivialFibreProduct
import Theorems.Thm_GlobalTheory_AbLaw_CubeOpen_isPullback_iso_comp


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
variable {S S' : Scheme.{0}} (φ : S' ⟶ S) (X Y : Over S)
namespace GlobalTheory.Exist.ProdOpen
theorem _root_.solution :
    IsPullback (prodMap φ X Y) ((Over.pullback φ).obj X ⊗ (Over.pullback φ).obj Y).hom
      (X ⊗ Y).hom φ := by
  have h := IsPullback.of_hasPullback (X ⊗ Y).hom φ
  have hw := Over.w (Functor.LaxMonoidal.μ (Over.pullback φ) X Y)
  haveI : IsIso (Functor.LaxMonoidal.μ (Over.pullback φ) X Y).left :=
    (Over.forget S').map_isIso (Functor.LaxMonoidal.μ (Over.pullback φ) X Y)
  rw [← hw]
  exact isPullback_iso_comp h _
end GlobalTheory.Exist.ProdOpen
