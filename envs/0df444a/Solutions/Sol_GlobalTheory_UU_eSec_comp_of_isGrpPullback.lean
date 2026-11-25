-- Prove2me | solution 1 for GlobalTheory.UU.eSec_comp_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:01:14.66567+00:00
-- url     : https://prove2.me/submissions/d17db1cf-a03e-484d-b357-434c5b465827

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ESecCompOfIsGrpPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


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
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}} {f : S' ⟶ S}
namespace GlobalTheory.UU
theorem _root_.solution {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (hφ : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have h1 : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  let P : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk ((η[G']).left ≫ φ) (by
    show ((η[G']).left ≫ φ) ≫ G.hom = (𝟙_ (Over S')).hom ≫ f
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w])
  have e := hφ.2 (𝟙_ (Over S')) η[G'] η[G'] P P rfl rfl
  have hP : P * P = P := by
    apply Over.OverMorphism.ext
    rw [e, ← h1, _root_.mul_one, h1]
    rfl
  have hP1 : P = 1 := mul_eq_left.mp hP
  have hl := congrArg Over.Hom.left hP1
  rw [Hom.one_def, Over.comp_left] at hl
  change (η[G']).left ≫ φ = _ at hl
  rw [hl]
  congr 1
end GlobalTheory.UU
