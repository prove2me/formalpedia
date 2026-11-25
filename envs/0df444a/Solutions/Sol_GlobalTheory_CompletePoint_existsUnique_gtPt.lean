-- Prove2me | solution 1 for GlobalTheory.CompletePoint.existsUnique_gtPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:20:12.748376+00:00
-- url     : https://prove2.me/submissions/e70baa49-65c6-4eb7-8431-dd1577937f09

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTorusExtensionPointOfGroupPoint
import Theorems.Thm_GlobalTheory_CompletePoint_corr_of_thick
import Theorems.Thm_GlobalTheory_CompletePoint_exists_gen_of_thick
import Theorems.Thm_GlobalTheory_CompletePoint_formEq_mult
import Theorems.Thm_GlobalTheory_existsUnique_over_of_isAdicFamily
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cPoint_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
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
open GlobalTheory GlobalTheory.CompletePoint
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
variable [IsLocalRing R] [IsAdicComplete I R] {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
namespace GlobalTheory.CompletePoint
theorem _root_.solution (y : ∀ e, Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left)
    (hw : ∀ e, y e ≫ (thickObj R I e G).hom = 𝟙 _)
    (hy : ∀ e, thickTrans R I e ≫ y (e + 1) = y e ≫ thickMap R I e G) :
    ∃! gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R)))), ∀ e,
      thick R I e ≫ gp.b.left = y e ≫ (U.gt e).pG.left ∧ ∀ χ z J, Good D.toPre.P.L z J →
        val (Y := Spec (CommRingCat.of R)) (gp.s χ) (thick R I e) z J = val ((U.gt e).t χ) (y e) z J := by
  have hL := D.toPre.P.isLB
  obtain ⟨b₀, ⟨hb₀, hb⟩, hbu⟩ := existsUnique_over_of_isAdicFamily (I := I) (𝟙 _) D.toPre.P.A.hom
    (f := fun e => y e ≫ (U.gt e).pG.left)
    (fun e => by
      show thickTrans R I e ≫ y (e + 1) ≫ _ = _
      rw [← Category.assoc, hy, Category.assoc, U.gt_q])
    (fun e => by
      rw [Category.assoc, Over.w (U.gt e).pG, Category.comp_id]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ thick R I e) (hw e)).trans (Category.id_comp _)))
  let b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.toPre.P.A := Over.homMk b₀ hb₀
  have hb' : ∀ e, thick R I e ≫ b.left = y e ≫ (U.gt e).pG.left := hb
  choose s hs vs using fun χ => exists_gen_of_thick I hL
    (fun e => TorusCoord.formEq_of_left b (U.gt e).pG (thick R I e) (y e) (hb' e) χ)
    (fun e => LB.pullGen _ _ _ ((U.gt e).t χ) (y e))
    (fun e => DVR.pullGen_isGen _ _ _ _ ((U.gt e).t_gen χ) _) (fun e z J hJ => by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [hy, Category.id_comp]
      exact (val_pull hJ _ _ _).symm.trans (val_corr hJ (U.gt_t e χ) (y e)))
  have vs' : ∀ χ e z J, Good D.toPre.P.L z J →
      val (s χ) (thick R I e) z J = val ((U.gt e).t χ) (y e) z J := fun χ e z J hJ => by
    refine (vs χ e z J hJ).trans ((val_pull hJ _ _ _).trans ?_)
    rw [Category.id_comp]
  have hm : ∀ χ χ', LB.Gen.Corr D.toPre.P.L _ _ _ _
      (LB.mulGen D.toPre.P.L _ _ _ _ (s (χ + χ'))
        (DegPre.cubAtT D.toPre _ (DegPre.cT D.toPre _ χ) (DegPre.cT D.toPre _ χ') b))
      (LB.mulGen D.toPre.P.L _ _ _ _ (s χ) (s χ')) := fun χ χ' =>
    corr_of_thick I hL (formEq_mult b χ χ')
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hs _) (DVR.pullGen_isGen _ _ _ _ D.toPre.cub.isGen _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hs _) (hs _)) fun e z J hJ => by
        refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
        refine Eq.trans (congrArg₂ (· * ·) (vs' _ e z J hJ) ((val_pull hJ _ _ _).trans ?_))
          ((TorusCoord.val_t_mul (U.gt e) (y e) χ χ' z J hJ).trans
            (congrArg₂ (· * ·) (vs' _ e z J hJ) (vs' _ e z J hJ)).symm)
        exact congrArg (fun q => TorusCoord.cubVal q z J)
          ((TorusCoord.comp_eq_of_left b (U.gt e).pG (thick R I e) (y e) (hb' e)).2 χ χ')
  have h0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (s 0) (LB.oneGen D.toPre.P.L) := corr_of_val hL fun z J hJ => by
    have h := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
      ((val_corr hJ (hm 0 0) (𝟙 _)).trans (val_mul hJ _ _ _))
    have c0 : DegPre.cT D.toPre (𝟙_ (Over (Spec (CommRingCat.of R)))) 0 = 1 := cPoint_zero _
    have c1 : TorusCoord.cubVal (𝟙 _ ≫ (lift (DegPre.cT D.toPre _ 0) (lift (DegPre.cT D.toPre _ 0) b)).left) z J
        = 1 := by
      rw [Category.id_comp, c0]
      exact (isCub_cubV D.toPre.cub hJ).face 1 b
    have key : ∀ {V : Type} [CommGroup V] (a c : V), c = 1 → a * c = a * a → a = 1 := fun a c hc h => by
      rw [hc] at h
      exact (mul_left_cancel h).symm
    rw [add_zero] at h
    exact (key _ _ c1 h).trans (val_one _).symm
  refine ⟨⟨b, s, hs, h0, hm⟩, fun e => ⟨hb' e, fun χ z J hJ => vs' χ e z J hJ⟩, ?_⟩
  rintro ⟨b', s', hs', _, _⟩ h
  obtain rfl : b' = b := Over.OverMorphism.ext (hbu b'.left ⟨Over.w b', fun e => (h e).1⟩)
  obtain rfl : s' = s := funext fun χ => TorusCoord.gen_eq_of_corr hL (hs' χ) (hs χ)
    (corr_of_thick I hL (fun _ _ _ => rfl) (hs' χ) (hs χ) fun e z J hJ =>
      ((h e).2 χ z J hJ).trans (vs' χ e z J hJ).symm)
  rfl
end GlobalTheory.CompletePoint
