-- Prove2me | solution 1 for GlobalTheory.TorusCoordPull.weight_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:31:47.872646+00:00
-- url     : https://prove2.me/submissions/5517ca85-be8e-44f8-a306-94fab1f62e4a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGrpPullbackThick
import Theorems.Thm_P2M_GlobalTheory_TorusCoordPull_exists_good__38f148e1dff0
import Theorems.Thm_GlobalTheory_TorusCoordPull_val_ratio_pull
import Theorems.Thm_GlobalTheory_TorusCoordPull_val_charGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorusCoordPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR TopologicalSpace
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {S S' : Scheme.{0}} {j : S ⟶ Spec (CommRingCat.of R)}
  {j' : S' ⟶ Spec (CommRingCat.of R')} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']
  [IsCommMonObj G'] (p : (Over.map j).obj G ⟶ D.P.A) (p' : (Over.map j').obj G' ⟶ D'.P.A) (h : G'.left ⟶ G.left)
  (hp : p'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ p.left)
  {σ : S' ⟶ S} (gp : IsGrpPullback G' G σ h) {χ : D'.X}
  {t : LB.Gen (LB.LinComb D.P.L (D.Oφ p (hD.xe χ)) Oinvε)} {a : LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' χ) Oinvε)}
  (H : PMaps hD.w (D'.Oφ p' χ) (D.Oφ p (hD.xe χ)) Oinvε a t h)
omit [IsCommMonObj G] [IsCommMonObj G']
include hp gp H
namespace GlobalTheory.TorusCoordPull
theorem _root_.solution (i : splitTorus S D.X ⟶ G) (i' : splitTorus S' D'.X ⟶ G')
    (hT : (splitTorus S' D'.X).left ⟶ (splitTorus S D.X).left) (hi : i'.left ≫ h = hT ≫ i.left)
    (hχ : hT.appTop.hom (charUnit _ D.X (hD.xe χ)).val = (charUnit _ D'.X χ).val)
    (aO : (Over.map j').map (lift (fst (splitTorus S' D'.X) G' ≫ i') (snd _ _) ≫ μ[G']) ≫ p' =
      (Over.map j').map (snd (splitTorus S' D'.X) G') ≫ p')
    (hw : LB.Gen.Corr D.P.L _ _ _ _
      (LB.pullGen D.P.L _ _ t (lift (fst (splitTorus S D.X) G ≫ i) (snd _ _) ≫ μ[G]).left)
      (LB.mulGen D.P.L _ _ _ _ (charGen D.X G D.P.L (hD.xe χ))
        (LB.pullGen D.P.L _ _ t (snd (splitTorus S D.X) G).left))) :
    LB.Gen.Corr D'.P.L _ _ _ _
      (LB.pullGen D'.P.L _ _ a (lift (fst (splitTorus S' D'.X) G' ≫ i') (snd _ _) ≫ μ[G']).left)
      (LB.mulGen D'.P.L _ _ _ _ (charGen D'.X G' D'.P.L χ)
        (LB.pullGen D'.P.L _ _ a (snd (splitTorus S' D'.X) G').left)) := by
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
  have wT : hT ≫ (splitTorus S D.X).hom = (splitTorus S' D'.X).hom ≫ σ := by
    rw [← Over.w i, ← Category.assoc, ← hi, Category.assoc, gp.1.w, ← Category.assoc, Over.w]
  obtain ⟨N, n₁, n₂, n₃⟩ : ∃ N : (splitTorus S' D'.X ⊗ G').left ⟶ (splitTorus S D.X ⊗ G).left,
      N ≫ (fst (splitTorus S D.X) G).left = (fst (splitTorus S' D'.X) G').left ≫ hT ∧
      N ≫ (snd (splitTorus S D.X) G).left = (snd (splitTorus S' D'.X) G').left ≫ h ∧
      N ≫ (lift (fst (splitTorus S D.X) G ≫ i) (snd _ _) ≫ μ[G]).left =
        (lift (fst (splitTorus S' D'.X) G' ≫ i') (snd _ _) ≫ μ[G']).left ≫ h := by
    let p₁ := fst (splitTorus S' D'.X) G'
    let pr := snd (splitTorus S' D'.X) G'
    refine ⟨(lift (pushPt wT p₁) (pushPt gp.1.w pr)).left,
      congrArg (fun q => q.left) (lift_fst (pushPt wT p₁) (pushPt gp.1.w pr)),
      congrArg (fun q => q.left) (lift_snd (pushPt wT p₁) (pushPt gp.1.w pr)), ?_⟩
    have : lift (pushPt wT p₁) (pushPt gp.1.w pr) ≫ (lift (fst (splitTorus S D.X) G ≫ i) (snd _ _) ≫ μ[G]) =
        (pushPt wT p₁ ≫ i) * pushPt gp.1.w pr :=
      (MonObj.comp_mul _ (fst _ _ ≫ i) (snd _ _)).trans (by rw [lift_fst_assoc, lift_snd])
    refine (congrArg (fun q => q.left) this).trans (gp.2 _ (p₁ ≫ i') pr _ _ ?_ rfl)
    show (p₁.left ≫ hT) ≫ i.left = (p₁.left ≫ i'.left) ≫ h
    rw [Category.assoc, Category.assoc, hi]
  have v₃ : val t (N ≫ (lift (fst (splitTorus S D.X) G ≫ i) (snd _ _) ≫ μ[G]).left) y J =
      gm (N ≫ (fst (splitTorus S D.X) G).left) y ⊤ (charUnit _ D.X (hD.xe χ)) *
        val t (N ≫ (snd (splitTorus S D.X) G).left) y J :=
    (val_pull hJ _ _ _).symm.trans ((val_corr hJ hw N).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))))
  have v₄ : gm ((fst (splitTorus S' D'.X) G').left ≫ hT) y ⊤ (charUnit _ D.X (hD.xe χ)) =
      gm (fst (splitTorus S' D'.X) G').left y ⊤ (charUnit _ D'.X χ) :=
    (gm_pull _ hT y ⊤ trivial _).symm.trans (congrArg (gm (fst (splitTorus S' D'.X) G').left y ⊤) (Units.ext hχ))
  rw [n₁, n₂, n₃, v₄] at v₃
  have v₅ := val_ratio_pull hD p p' h hp H _ _ aO (y := y) hJ hJ' _ v₃
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ ((val_mul hJ' _ _ _).trans
    (congrArg₂ (· * ·) (val_charGen _ _ _ _ _ _ _) (val_pull hJ' _ _ _))).symm)
  rw [Category.id_comp, Category.id_comp, Category.id_comp]
  exact v₅
end GlobalTheory.TorusCoordPull
