-- Prove2me | solution 1 for GlobalTheory.existsUnique_gtPt_of_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:37:54.485858+00:00
-- url     : https://prove2.me/submissions/ced0a3a1-cb65-45f9-84b8-0896f9a8b047

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTorusExtensionPointOfGroupPoint
import Theorems.Thm_GlobalTheory_CompletePoint_existsUnique_gtPt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G), ∃! gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R)))), (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) := by
  intro R _ _ _ I hR _ D A G _ _ U x
  have := hR.2.2.2
  have hx : x.left ≫ G.hom = 𝟙 _ := Over.w x
  have w : ∀ e, (thick R I e ≫ x.left) ≫ G.hom = 𝟙 _ ≫ thick R I e := fun e => by
    rw [Category.assoc, hx, Category.id_comp]; exact Category.comp_id _
  let y : ∀ e, Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left := fun e =>
    pullback.lift (thick R I e ≫ x.left) (𝟙 _) (w e)
  have y₁ : ∀ e, y e ≫ pullback.fst G.hom (thick R I e) = thick R I e ≫ x.left := fun e => pullback.lift_fst _ _ _
  have y₂ : ∀ e, y e ≫ (thickObj R I e G).hom = 𝟙 _ := fun e => pullback.lift_snd _ _ _
  have hy : ∀ e, thickTrans R I e ≫ y (e + 1) = y e ≫ thickMap R I e G := fun e => by
    have tf : thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    refine (cancel_mono (pullback.fst G.hom (thick R I (e + 1)))).1 ?_
    exact ((Category.assoc _ _ _).trans ((congrArg (thickTrans R I e ≫ ·) (y₁ (e + 1))).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ x.left) (thickTrans_comp R I e))))).trans
      ((Category.assoc _ _ _).trans ((congrArg (y e ≫ ·) tf).trans (y₁ e))).symm
  refine (existsUnique_congr fun gp => forall_congr' fun e => ⟨fun h => ?_, ?_⟩).1
    (GlobalTheory.CompletePoint.existsUnique_gtPt U y y₂ hy)
  · refine ⟨Over.homMk (y e) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ thick R I e) (y₂ e)).trans (Category.id_comp _))), Over.OverMorphism.ext (y₁ e),
      Over.OverMorphism.ext h.1.symm, fun χ => corr_of_val D.toPre.P.isLB fun z J hJ => ?_⟩
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    exact (congrArg (fun q => val _ q z J) (Category.id_comp _)).trans ((h.2 χ z J hJ).symm.trans
      (congrArg (fun q => val _ q z J) (Category.id_comp _)).symm)
  · rintro ⟨xe, h₁, h₂, h₃⟩
    have hxe : y e = xe.left := (cancel_mono (pullback.fst G.hom (thick R I e))).1
      ((y₁ e).trans (congrArg (·.left) h₁).symm)
    rw [hxe]
    refine ⟨(congrArg (·.left) h₂).symm, fun χ z J hJ => ?_⟩
    have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (h₃ χ) (𝟙 _)).trans (val_pull hJ _ _ _))
    rw [Category.id_comp, Category.id_comp] at this
    exact this.symm
end GlobalTheory
