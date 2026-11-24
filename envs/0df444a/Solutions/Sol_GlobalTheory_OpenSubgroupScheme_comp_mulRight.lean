-- Prove2me | solution 1 for GlobalTheory.OpenSubgroupScheme.comp_mulRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:16:15.32574+00:00
-- url     : https://prove2.me/submissions/4121d6e1-0999-44aa-9ba0-a86c3bb0464c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIsoOfIsOpenImmersionOfGeometricallyConnected

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
theorem _root_.solution [GrpObj G] (x g : 𝟙_ _ ⟶ G) : x ≫ (GrpObj.mulRight g).hom = x * g := by
  rw [GrpObj.mulRight_hom, Hom.mul_def, comp_lift_assoc, Category.comp_id, ← Category.assoc,
    Subsingleton.elim (x ≫ toUnit G) (𝟙 _), Category.id_comp]
end GlobalTheory.OpenSubgroupScheme
