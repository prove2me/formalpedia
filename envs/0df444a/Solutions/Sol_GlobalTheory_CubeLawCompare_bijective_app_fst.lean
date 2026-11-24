-- Prove2me | solution 1 for GlobalTheory.CubeLawCompare.bijective_app_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:22:10.572752+00:00
-- url     : https://prove2.me/submissions/43cf60b0-783a-43af-b69f-8f8c3d0cafeb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_RigidityTranslation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocallyTrivialOfIsoPull
import Theorems.Thm_GlobalTheory_CubeLawCompare_bijective_app_of_restrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CubeLawCompare
open scoped CategoryTheory.Obj
namespace GlobalTheory.CubeLawCompare
theorem _root_.solution (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A]
    (hA : IsAbelianScheme A) (T : Over S) (V : T.left.Opens) :
    Function.Bijective ((fst T A).left.app V).hom := by
  have hB : IsAbelianScheme ((Over.pullback (V.ι ≫ T.hom)).obj A) :=
    { comm := by have := hA.comm; infer_instance
      smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have h₁ : Function.Bijective (pullback.snd A.hom (V.ι ≫ T.hom)).appTop.hom := hG _ _ hB
  have sq : IsPullback ((pullback.fst T.hom A.hom ⁻¹ᵁ V).ι ≫ pullback.snd T.hom A.hom)
      (pullback.fst T.hom A.hom ∣_ V) A.hom (V.ι ≫ T.hom) :=
    (isPullback_morphismRestrict (pullback.fst T.hom A.hom) V).flip.paste_horiz
      (IsPullback.of_hasPullback T.hom A.hom).flip
  have h₂ : Function.Bijective (pullback.fst T.hom A.hom ∣_ V).appTop.hom := by
    rw [← sq.isoPullback_hom_snd, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso (sq.isoPullback.hom.app ⊤)).comp h₁
  exact bijective_app_of_restrict _ V h₂
end GlobalTheory.CubeLawCompare
