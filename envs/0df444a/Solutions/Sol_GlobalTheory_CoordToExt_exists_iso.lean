-- Prove2me | solution 1 for GlobalTheory.CoordToExt.exists_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:46:30.426797+00:00
-- url     : https://prove2.me/submissions/775983b2-f31a-471c-906b-57dcaf5c034c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
import Theorems.Thm_GlobalTheory_CoordToExt_refines_self
import Theorems.Thm_GlobalTheory_CoordToExt_Refines_exists_gen
import Theorems.Thm_GlobalTheory_CoordToExt_isGen_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen


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
variable {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.CoordToExt
theorem _root_.solution (hL : L.IsLB) {φ φ' : K → (Y ⟶ X)} (h : φ = φ') (ε : K → ℤ) :
    ∃ w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε), w.IsGen := by
  subst h
  refine ((refines_self φ ε).div (refines_self φ ε)).exists_gen hL (fun U _ f => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ((Fintype.prod_sum_type _).trans ?_))
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]
end GlobalTheory.CoordToExt
