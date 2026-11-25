-- Prove2me | solution 1 for GlobalTheory.CommutatorPairing.commVal_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:52:14.777972+00:00
-- url     : https://prove2.me/submissions/1443433f-18c6-4a86-a64e-c150e9188385

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Theorems.Thm_GlobalTheory_CommutatorPairing_thetaVal_ratio

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommutatorPairing
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T T' Z : Over S}
    (θx θy : ThetaGrp A L k T) (θx' θy' : ThetaGrp A L k T') (t : Z ⟶ T) (t' : Z ⟶ T')
    (hx : t ≫ θx.pt = t' ≫ θx'.pt) (hy : t ≫ θy.pt = t' ≫ θy'.pt) (a : Z ⟶ A) (z : Z.left) (J) (hJ : Good L z J) :
    commVal θx θy t a z J = commVal θx' θy' t' a z J := by
  obtain ⟨u, hu⟩ := thetaVal_ratio hG hA hL θx θx' t t' hx z
  obtain ⟨v, hv⟩ := thetaVal_ratio hG hA hL θy θy' t t' hy z
  rw [commVal, commVal, hu _ J hJ, hu _ J hJ, hv _ J hJ, hv _ J hJ, hx, hy]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.CommutatorPairing
