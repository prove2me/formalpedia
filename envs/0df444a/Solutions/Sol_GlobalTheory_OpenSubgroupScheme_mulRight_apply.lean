-- Prove2me | solution 1 for GlobalTheory.OpenSubgroupScheme.mulRight_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:32:40.792132+00:00
-- url     : https://prove2.me/submissions/52e39458-86de-4929-abd9-64aca959e9e6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIsoOfIsOpenImmersionOfGeometricallyConnected
import Theorems.Thm_GlobalTheory_OpenSubgroupScheme_comp_mulRight

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
open GlobalTheory
open GlobalTheory.OpenSubgroupScheme
variable {K : Type} [Field K] {Ga G : Over (Spec (CommRingCat.of K))}
namespace GlobalTheory.OpenSubgroupScheme
theorem _root_.solution [GrpObj G] (x g : 𝟙_ _ ⟶ G) :
    (GrpObj.mulRight g).hom.left (x.left (IsLocalRing.closedPoint K)) =
      (x * g).left (IsLocalRing.closedPoint K) := by
  rw [← comp_mulRight]; rfl
end GlobalTheory.OpenSubgroupScheme
