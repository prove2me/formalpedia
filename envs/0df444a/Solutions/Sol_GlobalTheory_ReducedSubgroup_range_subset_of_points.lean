-- Prove2me | solution 1 for GlobalTheory.ReducedSubgroup.range_subset_of_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:31.004123+00:00
-- url     : https://prove2.me/submissions/614bfaa2-abe7-4c0f-bbee-3c36e57455f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField

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
open GlobalTheory GlobalTheory.ReducedSubgroup
namespace GlobalTheory.ReducedSubgroup
theorem _root_.solution {k : Type} [Field k] [IsAlgClosed k] {T B : Over (Sp k)}
    [LocallyOfFiniteType T.hom] (g : T ⟶ B) {Z : Set B.left} (hZ : IsClosed Z)
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ T, Set.range (x ≫ g).left ⊆ Z) : Set.range g.left ⊆ Z := by
  have := LocallyOfFiniteType.jacobsonSpace T.hom
  rintro _ ⟨t, rfl⟩
  by_contra ht
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints (Z := (g.left ⁻¹' Z)ᶜ) ⟨t, ht⟩
    (hZ.preimage g.left.continuous).isOpen_compl.isLocallyClosed
  let x' : 𝟙_ (Over (Sp k)) ⟶ T :=
    Over.homMk (pointOfClosedPoint T.hom x hxc) (pointOfClosedPoint_comp T.hom x hxc)
  refine hx (h x' ⟨IsLocalRing.closedPoint k, ?_⟩)
  exact congrArg g.left (pointOfClosedPoint_apply T.hom x hxc _)
end GlobalTheory.ReducedSubgroup
