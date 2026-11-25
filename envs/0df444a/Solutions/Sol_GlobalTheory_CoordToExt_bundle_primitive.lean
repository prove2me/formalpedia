-- Prove2me | solution 1 for GlobalTheory.CoordToExt.bundle_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:56:01.796181+00:00
-- url     : https://prove2.me/submissions/c17d1aff-c50b-4925-b14a-be19324b7219

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
import Theorems.Thm_GlobalTheory_CoordToExt_refines_self
import Theorems.Thm_GlobalTheory_CoordToExt_Refines_linComb
import Theorems.Thm_GlobalTheory_CoordToExt_Refines_exists_gen
import Theorems.Thm_GlobalTheory_CoordToExt_prod_square
import Theorems.Thm_GlobalTheory_CoordToExt_prod_O
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_O__comp_24bcd133e28a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
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
theorem _root_.solution (χ : D.X) : ∃ t : LB.Gen (abelian₂ (thickObj R I e D.P.A) (bundle I D e χ)), t.IsGen := by
  let ρ := pushHom (isGrpPullback_pullback D.P.A (thick R I e)) (G2 (thickObj R I e D.P.A))
  have hρ : ∀ (x : G2 (thickObj R I e D.P.A) ⟶ thickObj R I e D.P.A) k,
      x.left ≫ D.Oφ (D.prBe I e) χ k = D.Oφ (ρ x) χ k := fun x k =>
    WeightPf.Oφ_comp (T' := Over.mk ((G2 (thickObj R I e D.P.A)).hom ≫ thick R I e))
      ((Over.map (thick R I e)).map x) (D.prBe I e) χ k
  refine ((refines_self _ _).linComb _ _).exists_gen D.P.isLB (fun U _ h => ?_)
    _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (toUnit _ ≫ D.c χ) (lift (ρ (x2 _ 0)) (ρ (x2 _ 1)))).left)
  refine (prod_cub (toUnit _ ≫ D.c χ) (ρ (x2 _ 0)) (ρ (x2 _ 1)) h).trans (Eq.symm ?_)
  rw [Fintype.prod_prod_type]
  simp only [zpow_mul, Finset.prod_zpow, hρ]
  refine (prod_square (x2 (thickObj R I e D.P.A)) (fun x => ∏ k, h (D.Oφ (ρ x) χ k) ^ Oε k)).trans ?_
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_O D (ρ _) _ h) (congrArg (·⁻¹) (prod_O D (ρ _) _ h)))
    (congrArg (·⁻¹) (prod_O D (ρ _) _ h))) (prod_O D (ρ _) _ h)).trans ?_
  rw [map_one, map_mul, _root_.mul_one, ← _root_.mul_assoc (toUnit _ ≫ D.c χ)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.CoordToExt
