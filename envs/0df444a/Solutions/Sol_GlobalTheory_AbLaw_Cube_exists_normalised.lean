-- Prove2me | solution 1 for GlobalTheory.AbLaw.Cube.exists_normalised
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:41:24.635895+00:00
-- url     : https://prove2.me/submissions/00455aa9-3964-4548-a443-1fd557882d83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalOfNormalised
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
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
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Cube
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable [IsCommMonObj A] {L : LB A.left}
namespace GlobalTheory.AbLaw.Cube
theorem _root_.solution (hL : L.IsLB) (t : LB.Gen (Theta A L)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (Theta A L), t'.IsGen ∧ IsNormalised t' := by
  obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _
          (c := ∏ i, k (thφ A (x3 A) i) ^ thε i) rfl
          (DVR.prod_neg _ _ (prod_cub (1 : G3 A ⟶ A) 1 1 k))) ?_
      simp)
    (LB.mulGen L (thφ A (x3 A)) thε _ _ t (LB.invGen L _ _
      (LB.pullGen L (thφ A (x3 A)) thε t (lift (1 : G3 A ⟶ A) (lift 1 1)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨t', ht', fun y J hJ => ?_⟩
  refine (hv _ _ y J hJ).trans ((val_mul hJ _ _ _).trans ((congrArg _ (val_inv _ _)).trans
    (mul_inv_eq_one.2 (Eq.symm ((val_pull hJ _ _ _).trans ?_)))))
  rw [← Over.comp_left, comp_lift, comp_lift, MonObj.comp_one]
  rfl
end GlobalTheory.AbLaw.Cube
