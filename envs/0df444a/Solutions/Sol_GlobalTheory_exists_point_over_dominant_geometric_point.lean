-- Prove2me | solution 1 for GlobalTheory.exists_point_over_dominant_geometric_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:45:52.140796+00:00
-- url     : https://prove2.me/submissions/6bdcf90e-b43d-42cb-bd73-ec56e6a74d36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqOfDominantGeometricPointsOfUnramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {U S : Scheme.{u}} (g : U ⟶ S)
    [UniversallyOpen g] [LocallyOfFiniteType g] [Nonempty U] {F : Type u} [Field F]
    [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t] :
    ∃ j : Spec (.of F) ⟶ U, j ≫ g = t := by
  obtain ⟨z, u, hu⟩ := t.denseRange.exists_mem_open g.isOpenMap.isOpen_range
    (Set.range_nonempty _)
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := t) u z hu
  have : JacobsonSpace ↥(pullback g t) := LocallyOfFiniteType.jacobsonSpace (pullback.snd g t)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback g t)))
    ⟨w, trivial⟩ isOpen_univ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨pointOfClosedPoint (pullback.snd g t) c hc ≫ pullback.fst g t, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
end GlobalTheory
