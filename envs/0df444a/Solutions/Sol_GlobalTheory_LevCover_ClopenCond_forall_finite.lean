-- Prove2me | solution 1 for GlobalTheory.LevCover.ClopenCond.forall_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:34.689119+00:00
-- url     : https://prove2.me/submissions/fd42e019-365d-438f-9657-15801eac093d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {S : Scheme.{0}}
namespace GlobalTheory.LevCover
namespace ClopenCond
theorem _root_.solution {T : Over S} {J : Type} [Finite J] {P : J → ∀ T' : Over S, (T' ⟶ T) → Prop}
    (h : ∀ i, ClopenCond T (P i)) : ClopenCond T fun T' h => ∀ i, P i T' h := by
  choose U hU H using h
  refine ⟨⟨⋂ i, (U i : Set T.left), isOpen_iInter_of_finite fun i => (U i).isOpen⟩, isClosed_iInter hU,
    fun T' h => ?_⟩
  simp only [H, TopologicalSpace.Opens.coe_mk, Set.subset_iInter_iff]
end ClopenCond
end GlobalTheory.LevCover
