-- Prove2me | solution 1 for GlobalTheory.PointsCompact.continuous_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:27:16.161527+00:00
-- url     : https://prove2.me/submissions/5f6e6c0f-fd36-41e5-a3a5-da946294aece

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CompactSpacePointsPolAV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.PointsCompact
namespace GlobalTheory.PointsCompact
theorem _root_.solution (h1 : ValueRules) {X Y : Over (Sp ℂ)} (φ : X ⟶ Y) :
    @Continuous _ _ (pointTopology X) (pointTopology Y) (fun x => x ≫ φ) := by
  letI := pointTopology X
  refine continuous_generateFrom_iff.2 ?_
  rintro S ⟨U, f, O, hO, rfl⟩
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  refine ⟨φ.left ⁻¹ᵁ U, (φ.left.app U).hom f, O, hO, ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Over.comp_left]
  rw [(h1 _ x.left).2.2.2.1 _ φ.left U f]
  exact Iff.rfl
end GlobalTheory.PointsCompact
