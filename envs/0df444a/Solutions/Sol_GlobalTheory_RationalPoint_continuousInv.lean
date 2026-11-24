-- Prove2me | solution 1 for GlobalTheory.RationalPoint.continuousInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:48:50.107092+00:00
-- url     : https://prove2.me/submissions/e1cbcd98-814d-4eb1-b38c-b9eaee0788ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Theorems.Thm_GlobalTheory_RationalPoint_continuous_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology
open GlobalTheory
open GlobalTheory.RationalPoint
variable {k : Type} [Field k]
namespace GlobalTheory.RationalPoint
theorem _root_.solution (B : Over (Sp k)) [GrpObj B] :
    @ContinuousInv (𝟙_ (Over (Sp k)) ⟶ B) (zariski B) _ := by
  letI := zariski B
  refine ⟨?_⟩
  convert continuous_comp (𝟙 B)⁻¹ using 2 with y
  rw [GrpObj.comp_inv, Category.comp_id]
end GlobalTheory.RationalPoint
