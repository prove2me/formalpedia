-- Prove2me | solution 1 for GlobalTheory.PsiSpread.Extends.cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:16:07.011367+00:00
-- url     : https://prove2.me/submissions/907c2e1b-2fb9-43f5-9c9d-f358712c5128

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteCubeInduction
import Theorems.Thm_GlobalTheory_PsiSpread_prod_elim
import Theorems.Thm_GlobalTheory_PsiSpread_prod_punit
import Theorems.Thm_GlobalTheory_TauPull_val_tau
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PsiSpread
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.PsiSpread
namespace Extends
theorem _root_.solution (hB : D.TauBimult) {T : Over (Spec (CommRingCat.of R))} (κ : TK R ⟶ T) (a a' b : D.X)
    (h₁ : Extends D κ a) (h₂ : Extends D κ a') (h₃ : Extends D κ b) (h₄ : Extends D κ (a + a'))
    (h₅ : Extends D κ (a + b)) (h₆ : Extends D κ (a' + b)) : Extends D κ (a + a' + b) := by
  obtain ⟨t₁, g₁, v₁⟩ := h₁
  obtain ⟨t₂, g₂, v₂⟩ := h₂
  obtain ⟨t₃, g₃, v₃⟩ := h₃
  obtain ⟨t₄, g₄, v₄⟩ := h₄
  obtain ⟨t₅, g₅, v₅⟩ := h₅
  obtain ⟨t₆, g₆, v₆⟩ := h₆
  obtain ⟨t, gt, vt⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => (cP D T (a + a' + b)).left) (ε' := fun _ => -1)
    (fun U _ h => by
      have p := prod_cub (cP D T a) (cP D T a') (cP D T b) h
      have q : (toUnit T).left ≫ eSec D.P.A = (1 : T ⟶ D.P.A).left := rfl
      refine (prod_elim h (prod_elim h (prod_elim h (prod_punit h _ _) (prod_punit h _ _)) (prod_punit h _ _))
        (prod_neg _ _ (prod_elim h (prod_elim h (prod_elim h (prod_punit h _ _) (prod_punit h _ _)) (prod_punit h _ _))
          (prod_elim h (prod_punit h _ _) p)))).trans (Eq.trans ?_ (prod_punit h _ _).symm)
      rw [q]
      simp only [cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      abel)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t₄ t₅) t₆)
      (LB.invGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t₁ t₂) t₃)
        (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ D.rig (toUnit T).left)
          (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (cP D T a) (lift (cP D T a') (cP D T b))).left)))))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ g₄ g₅) g₆)
      (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ g₁ g₂) g₃)
        (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) (pullGen_isGen _ _ _ _ D.cub.isGen _)))))
  refine ⟨t, gt, fun z J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
  have c : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      th D z J (cP D _ a) (cP D _ a') (cP D _ b) :=
    (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ a) (cP D _ a') (cP D _ b)).trans (by simp only [comp_cP])
  have vρ : val (LB.pullGen D.P.L _ _ D.rig (toUnit T).left) κ.left z J = val D.rigK (𝟙 _) z J := by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp]
    exact congrArg (fun q => val D.rig q z J) (Over.w κ)
  have vc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (cP D T a) (lift (cP D T a') (cP D T b))).left) κ.left z J = th D z J (cP D _ a) (cP D _ a') (cP D _ b) :=
    (val_cub D.cub κ hJ _ _ _).trans (by simp only [comp_cP])
  rw [c, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ] at e
  refine (vt _ _ z J hJ).trans (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (v₄ z J hJ) (v₅ z J hJ))) (v₆ z J hJ)))
    ((val_inv _ _).trans (congrArg (·⁻¹) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (v₁ z J hJ) (v₂ z J hJ))) (v₃ z J hJ)))
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) vρ vc)))))))).trans ?_)
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) -e'
end Extends
end GlobalTheory.PsiSpread
