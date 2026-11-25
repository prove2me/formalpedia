-- Prove2me | solution 1 for GlobalTheory.PrimCocycle.exists_normalised
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:07:36.580828+00:00
-- url     : https://prove2.me/submissions/3d0bddbb-a399-4d34-bcca-f99989321334

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
import Theorems.Thm_GlobalTheory_PrimCocycle_prod_lam
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PrimCocycle
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
namespace GlobalTheory.PrimCocycle
theorem _root_.solution {L : LB B.left} (hL : L.IsLB) (t : LB.Gen (LB.LinComb L (lamφ B) lamε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L (lamφ B) lamε), u.IsGen ∧
      ∀ (T : Over S) (z : T.left) (J), Good L z J → val₂ u z J (1 : T ⟶ B) 1 = 1 := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := lamφ B) (ε' := lamε)
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := V) _
        (c := ∏ i, k (lamφ B i) ^ lamε i) rfl
        (DVR.prod_neg _ _ (prod_lam (1 : B ⊗ B ⟶ B) (1 : B ⊗ B ⟶ B) k))) ?_
      simp)
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (lift (1 : B ⊗ B ⟶ B) (1 : B ⊗ B ⟶ B)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨u, hu, fun T z J hJ => ?_⟩
  have : (lift (1 : T ⟶ B) (1 : T ⟶ B)).left ≫ (lift (1 : B ⊗ B ⟶ B) (1 : B ⊗ B ⟶ B)).left =
      (lift (1 : T ⟶ B) (1 : T ⟶ B)).left := by
    rw [← Over.comp_left, comp_lift, MonObj.comp_one]
  rw [val₂, hv _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]
end GlobalTheory.PrimCocycle
