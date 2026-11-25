-- Prove2me | solution 1 for GlobalTheory.CubTrivTorus.connectedSpace_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:58:32.256835+00:00
-- url     : https://prove2.me/submissions/e777d8ff-e0db-4ce8-98d1-226a598d6be7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Theorems.Thm_GlobalTheory_GroupConn_connectedSpace_group


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubTrivTorus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
namespace GlobalTheory.CubTrivTorus
theorem _root_.solution [ConnectedSpace S] [Module.Free ℤ X] : ConnectedSpace (splitTorus S X).left := by
  have hS : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›
  haveI : Smooth (𝟙_ (Over S)).hom := by show Smooth (𝟙 S); infer_instance
  haveI : GeometricallyConnected (𝟙_ (Over S)).hom := by show GeometricallyConnected (𝟙 S); infer_instance
  obtain ⟨h, -⟩ := (GlobalTheory.GroupConn.connectedSpace_group S (𝟙_ (Over S))).2 X (𝟙_ (Over S)) hS
  haveI : ConnectedSpace ((Over.forget S).obj (splitTorus S X ⊗ 𝟙_ (Over S))) := h
  let e := (Over.forget S).mapIso (ρ_ (splitTorus S X))
  exact (Scheme.homeoOfIso e).surjective.connectedSpace (Scheme.homeoOfIso e).continuous
end GlobalTheory.CubTrivTorus
