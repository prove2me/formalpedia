-- Prove2me | solution 1 for GlobalTheory.UU.TQ.exists_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:36:15.552699+00:00
-- url     : https://prove2.me/submissions/d4e6dbeb-931f-4b9f-bcb7-303d663fa66e

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
import Theorems.Thm_GlobalTheory_UU_isPullback_kernel_baseChange
import Theorems.Thm_GlobalTheory_UU_isPullback_pullback_map_left
import Theorems.Thm_GlobalTheory_SplitTorus_bcIso_hom_fst
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_GlobalTheory_flatQuotient_iso_of_same_kernel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_of_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


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
namespace TQ
theorem _root_.solution : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] (G : Over S)
    [GrpObj G] (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F →
    ∀ (Q : TQ G X) (Q' : TQ G' X), TorusCompat f F Q'.i Q.i →
    ∃ β : Q'.B.left ⟶ Q.B.left, Q'.q.left ≫ β = F ≫ Q.q.left ∧ IsGrpPullback Q'.B Q.B f β := by
  intro S S' f X _ G _ G' _ F hF Q Q' hT
  obtain ⟨e, he, heF⟩ := grpPullback_iso hF (isGrpPullback_pullback G f)
  have := Q.q_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have := Q'.q_affine
  have sq := isPullback_pullback_map_left f Q.q
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hi : Q'.i ≫ e.hom = (SplitTorus.bcIso f X).hom ≫ (Over.pullback f).map Q.i := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have a := (isPullback_pullback_map_left f Q.i).w
    have b := SplitTorus.bcIso_hom_fst f X
    exact ((Category.assoc _ _ _).trans ((congrArg (Q'.i.left ≫ ·) heF).trans (torusCompat_iff.1 hT).symm)).trans
      ((congrArg (· ≫ Q.i.left) b.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) a).trans (Category.assoc _ _ _).symm)))
  have hk : IsPullback Q'.i (toUnit _) (e.hom ≫ (Over.pullback f).map Q.q) (η[(Over.pullback f).obj Q.B]) := by
    refine (isPullback_kernel_baseChange f Q.isKernel).of_iso (SplitTorus.bcIso f X).symm e.symm (Iso.refl _)
      (Iso.refl _) ?_ (toUnit_unique _ _) (by simp) (by simp)
    rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hi, Iso.inv_hom_id_assoc]
  have h₁ : Flat ((Over.pullback f).map Q.q).left := MorphismProperty.of_isPullback (P := @Flat) sq inferInstance
  have h₂ : Surjective ((Over.pullback f).map Q.q).left :=
    MorphismProperty.of_isPullback (P := @Surjective) sq inferInstance
  have h₃ : QuasiCompact ((Over.pullback f).map Q.q).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  obtain ⟨β, hβ, hq⟩ := flatQuotient_iso_of_same_kernel S' G' ((Over.pullback f).obj Q.B) Q'.B _ _
    (e.hom ≫ (Over.pullback f).map Q.q) Q'.i Q'.q Q'.i inferInstance Q'.i_hom
    (by rw [Over.comp_left]; infer_instance) (by rw [Over.comp_left]; infer_instance)
    (by rw [Over.comp_left]; infer_instance) hk Q'.q_hom Q'.i_hom Q'.q_flat Q'.q_surj inferInstance Q'.isKernel
    hk.w Q'.isKernel.w
  refine ⟨β.hom.left ≫ pullback.fst Q.B.hom f, ?_,
    ((isGrpPullback_of_iso β).comp (isGrpPullback_pullback Q.B f)).congr (Category.id_comp f) rfl⟩
  rw [← Category.assoc, ← Over.comp_left, hq, Over.comp_left, Category.assoc, ← heF, Category.assoc]
  exact congrArg (_ ≫ ·) sq.w.symm
end TQ
end GlobalTheory.UU
