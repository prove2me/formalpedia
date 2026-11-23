-- Prove2me | solution 1 for GlobalTheory.RationalPoint.exists_pt_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:05.864882+00:00
-- url     : https://prove2.me/submissions/a13e6912-838b-4daa-aecf-25bc0f99c1ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup

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
variable [IsAlgClosed k]
namespace GlobalTheory.RationalPoint
theorem _root_.solution {X : Over (Sp k)} [LocallyOfFiniteType X.hom] {Z : Set X.left}
    (hZ : IsClosed Z) (hne : Z.Nonempty) : ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, pt x ∈ Z := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints hne hZ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc), ?_⟩
  have : pt (Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc) :
      𝟙_ (Over (Sp k)) ⟶ X) = c := pointOfClosedPoint_apply X.hom c hc _
  rwa [this]
end GlobalTheory.RationalPoint
