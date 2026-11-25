-- Prove2me | solution 1 for GlobalTheory.CoordToExt.bundle_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:48:18.53769+00:00
-- url     : https://prove2.me/submissions/3cf3b92e-653d-467c-983d-629307dca5f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
import Theorems.Thm_GlobalTheory_CoordToExt_refines_self
import Theorems.Thm_GlobalTheory_CoordToExt_Refines_exists_gen
import Theorems.Thm_GlobalTheory_CoordToExt_prod_O
import Theorems.Thm_GlobalTheory_CoordToExt_c_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub


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
open GlobalTheory
open GlobalTheory.CoordToExt
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ)
namespace GlobalTheory.CoordToExt
theorem _root_.solution (χ χ' : D.X) :
    ∃ t : LB.Iso (bundle I D e χ') (LB.div (bundle I D e (χ + χ')) (bundle I D e χ)), t.IsGen := by
  refine (((refines_self _ _).div (refines_self _ _)).div (refines_self _ _)).exists_gen D.P.isLB (fun U _ h => ?_)
    _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') (D.prBe I e))).left)
  refine (prod_cub (toUnit _ ≫ D.c χ) (toUnit _ ≫ D.c χ') (D.prBe I e) h).trans (Eq.symm ?_)
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_O D (D.prBe I e) _ h) (congrArg (·⁻¹) (prod_O D (D.prBe I e) _ h)))
    (congrArg (·⁻¹) (prod_O D (D.prBe I e) _ h))).trans ?_
  rw [c_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.CoordToExt
