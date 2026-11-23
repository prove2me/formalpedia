-- Prove2me | solution 1 for GlobalTheory.ReducedSubgroup.vanishingIdeal_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:02.870978+00:00
-- url     : https://prove2.me/submissions/163ce056-c6b6-4c66-8e21-63a8f816a084

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
universe u
open Scheme.IdealSheafData
namespace GlobalTheory.ReducedSubgroup
theorem _root_.solution {T X : Scheme.{u}} [IsReduced T] (g : T ⟶ X)
    (Z : TopologicalSpace.Closeds X) (h : Set.range g ⊆ Z) : vanishingIdeal Z ≤ g.ker := by
  refine le_ofIdeals_iff.mpr fun U a ha => ?_
  rw [RingHom.mem_ker, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen, eq_bot_iff]
  intro t ht
  have h1 : g t ∈ (vanishingIdeal Z).support := h ⟨t, rfl⟩
  have h2 := ((coe_support_inter (vanishingIdeal Z) U).le
    ⟨h1, X.basicOpen_le a ht⟩).1
  exact ((Scheme.mem_zeroLocus_iff _ _ _).mp h2 a ha ht).elim
end GlobalTheory.ReducedSubgroup
