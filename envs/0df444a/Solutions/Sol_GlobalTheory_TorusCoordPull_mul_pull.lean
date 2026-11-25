-- Prove2me | solution 1 for GlobalTheory.TorusCoordPull.mul_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:04:57.041071+00:00
-- url     : https://prove2.me/submissions/4a0e8c53-96c2-47ec-80da-6acaf1913e9e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGrpPullbackThick
import Theorems.Thm_GlobalTheory_TorusCoordPull_val_of_pmaps
import Theorems.Thm_P2M_GlobalTheory_TorusCoordPull_exists_good__38f148e1dff0
import Theorems.Thm_GlobalTheory_TorusCoordPull_prod_O
import Theorems.Thm_GlobalTheory_TorusCoordPull_push_cP
import Theorems.Thm_GlobalTheory_TorusCoordPull_over_base
import Theorems.Thm_P2M_GlobalTheory_TorusCoordPull_O__pull_be9eb376d61b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cub_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubeMap_comp_proj_three
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_hom_ext_triple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
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
  {D' : DegPre R'}
variable (hD : IsPullDeg φ D D') {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of R'))}
  (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left)
  (hp : p'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ p.left)
include hp
namespace GlobalTheory.TorusCoordPull
theorem _root_.solution (hG : GlobalFnsSt) (t : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (D.Oφ p χ) Oinvε))
    (a : ∀ χ : D'.X, LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' χ) Oinvε))
    (H : ∀ x, PMaps hD.w (D'.Oφ p' x) (D.Oφ p (hD.xe x)) Oinvε (a x) (t (hD.xe x)) h)
    (hm : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (t (χ + χ'))
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
          (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') p)).left))
      (LB.mulGen D.P.L _ _ _ _ (t χ) (t χ'))) (χ χ' : D'.X) :
    LB.Gen.Corr D'.P.L _ _ _ _
      (LB.mulGen D'.P.L _ _ _ _ (a (χ + χ'))
        (LB.pullGen D'.P.L (thφ D'.P.A (x3 D'.P.A)) thε D'.cub.t
          (lift (toUnit _ ≫ D'.c χ) (lift (toUnit _ ≫ D'.c χ') p')).left))
      (LB.mulGen D'.P.L _ _ _ _ (a χ) (a χ')) := by
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
  let U : Over.mk (T'.hom ≫ spMap φ) ⟶ T := Over.homMk h (over_base hD p p' h hp)
  have e : pushPt (pull_grp hD).1.w p' = U ≫ p := Over.OverMorphism.ext hp
  have va : ∀ x, val (t (hD.xe x)) h y J = (om hD.w y J J' (p' * cP D' T' x).left)⁻¹ *
      om hD.w y J J' (cP D' T' x).left * om hD.w y J J' p'.left * (om hD.w y J J' (1 : T' ⟶ D'.P.A).left)⁻¹ *
      val (a x) (𝟙 _) y J' := fun x => by
    have := val_of_pmaps (Oφ_pull hD p p' h hp x) (H x) (𝟙 _) hJ hJ'
    simp only [Category.id_comp] at this
    rw [this, prod_O]
  have c := cub_pull hG hD (T' := T') hJ hJ' (cP D' T' χ) (cP D' T' χ') p'
  have q : (lift (cP D' T' χ) (lift (cP D' T' χ') p')).left ≫ (cubeMapOf (pull_grp hD)).F3 =
      h ≫ (lift (cP D T (hD.xe χ)) (lift (cP D T (hD.xe χ')) p)).left := by
    refine Eq.trans (hom_ext_triple _ fun i => ?_ : _ = (lift (pushPt (pull_grp hD).1.w (cP D' T' χ))
      (lift (pushPt (pull_grp hD).1.w (cP D' T' χ')) (pushPt (pull_grp hD).1.w p'))).left) ?_
    · rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    · rw [push_cP, push_cP, e, ← comp_cP D U, ← comp_cP D U (hD.xe χ'), ← comp_lift, ← comp_lift]
      rfl
  rw [q] at c
  replace c := c.trans (congrArg₂ (· * ·) (prod_cub (cP D' T' χ) (cP D' T' χ') p' (om hD.w y J J')) rfl)
  have m : val (t (hD.xe χ + hD.xe χ')) h y J *
      val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
        (h ≫ (lift (cP D T (hD.xe χ)) (lift (cP D T (hD.xe χ')) p)).left) y J =
      val (t (hD.xe χ)) h y J * val (t (hD.xe χ')) h y J :=
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
      ((val_corr hJ (hm (hD.xe χ) (hD.xe χ')) h).trans (val_mul hJ _ _ _))
  rw [← map_add] at m
  replace m := (congrArg₂ (· * ·) rfl c).symm.trans m
  rw [va, va, va, cPoint_add, mul_comm p', mul_comm p', mul_comm p'] at m
  have vc := val_cub D'.cub (𝟙 T') hJ' (cP D' T' χ) (cP D' T' χ') p'
  rw [Category.id_comp, Category.id_comp, Category.id_comp] at vc
  refine ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl vc)).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  show val (a (χ + χ')) (𝟙 T'.left) y J' * cubV D'.cub y J' (cP D' T' χ) (cP D' T' χ') p' =
    val (a χ) (𝟙 T'.left) y J' * val (a χ') (𝟙 T'.left) y J'
  apply Additive.ofMul.injective
  have m' := congrArg Additive.ofMul m
  simp only [ofMul_mul, ofMul_inv] at m' ⊢
  linear_combination (norm := abel) m'
end GlobalTheory.TorusCoordPull
