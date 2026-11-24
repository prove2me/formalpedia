-- Prove2me | solution 1 for GlobalTheory.OpenSubgroupScheme.exists_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:18:45.211233+00:00
-- url     : https://prove2.me/submissions/d07658bd-0746-49fc-996e-ef82ab72f394

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
theorem _root_.solution [IsAlgClosed K] [LocallyOfFiniteType G.hom] (y : G.left) (hy : IsClosed {y}) :
    ∃ x : 𝟙_ _ ⟶ G, x.left (IsLocalRing.closedPoint K) = y :=
  ⟨Over.homMk (pointOfClosedPoint G.hom y hy) (pointOfClosedPoint_comp G.hom y hy),
    pointOfClosedPoint_apply G.hom y hy _⟩
end GlobalTheory.OpenSubgroupScheme
