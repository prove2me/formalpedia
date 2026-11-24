-- Prove2me | solution 1 for GlobalTheory.LevCover.clopenCond_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:46.989448+00:00
-- url     : https://prove2.me/submissions/19f458a8-3b5b-495a-ab05-d9eb6e982ebc

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
theorem _root_.solution {T Z : Over S} [IsFinite Z.hom] [Etale Z.hom] (u u' : T ⟶ Z) :
    ClopenCond T fun _ h => h ≫ u = h ≫ u' := by
  refine ⟨(FinEt.agreeι u u').opensRange, (FinEt.agreeι u u').isClosedEmbedding.isClosed_range, fun T' h => ?_⟩
  refine Iff.trans ?_ (FinEt.comp_eq_comp_iff_range u u' h.left)
  exact ⟨fun e => congrArg CommaMorphism.left e, fun e => Over.OverMorphism.ext e⟩
end GlobalTheory.LevCover
