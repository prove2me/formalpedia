-- Prove2me | solution 1 for GlobalTheory.LevCover.ClopenCond.and
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:16.083157+00:00
-- url     : https://prove2.me/submissions/4e358829-bb06-4263-a617-8fbfbc840188

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
theorem _root_.solution {T : Over S} {P P' : ∀ T' : Over S, (T' ⟶ T) → Prop} (h : ClopenCond T P)
    (h' : ClopenCond T P') : ClopenCond T fun T' h => P T' h ∧ P' T' h := by
  obtain ⟨U, hU, H⟩ := h
  obtain ⟨U', hU', H'⟩ := h'
  refine ⟨U ⊓ U', hU.inter hU', fun T' h => ?_⟩
  beta_reduce
  rw [H, H', TopologicalSpace.Opens.coe_inf, Set.subset_inter_iff]
end ClopenCond
end GlobalTheory.LevCover
