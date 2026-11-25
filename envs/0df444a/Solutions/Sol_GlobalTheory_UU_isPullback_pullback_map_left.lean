-- Prove2me | solution 1 for GlobalTheory.UU.isPullback_pullback_map_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:01:32.509403+00:00
-- url     : https://prove2.me/submissions/1f2fa2bd-0c68-4e2d-a2b5-8ccee2b3df1d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackKernelBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution {S S' : Scheme.{0}} (f : S' ⟶ S) {G B : Over S} (q : G ⟶ B) :
    IsPullback (pullback.fst G.hom f) ((Over.pullback f).map q).left q.left (pullback.fst B.hom f) := by
  have h₁ : IsPullback (pullback.fst G.hom f) (((Over.pullback f).map q).left ≫ pullback.snd B.hom f)
      (q.left ≫ B.hom) f := by
    have : ((Over.pullback f).map q).left ≫ pullback.snd B.hom f = pullback.snd G.hom f :=
      Over.w ((Over.pullback f).map q)
    rw [this, Over.w]
    exact IsPullback.of_hasPullback _ _
  exact h₁.of_bot (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)
end GlobalTheory.UU
