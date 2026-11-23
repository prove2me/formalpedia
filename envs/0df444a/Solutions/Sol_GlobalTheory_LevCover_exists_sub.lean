-- Prove2me | solution 1 for GlobalTheory.LevCover.exists_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:24.488071+00:00
-- url     : https://prove2.me/submissions/72bace02-1f02-4c34-ae70-9bcb1a1c5712

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom
import Theorems.Thm_GlobalTheory_LevCover_RepTors_ext
import Theorems.Thm_GlobalTheory_FinEt_range_subset_iff_factors


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
theorem _root_.solution {Z : Over S} [IsFinite Z.hom] [Etale Z.hom] (U : Z.left.Opens) (hU : IsClosed (U : Set Z.left)) :
    ∃ (V : Over S) (i : V ⟶ Z), IsFinite V.hom ∧ Etale V.hom ∧ Mono i ∧
      ∀ (T : Over S) (h : T ⟶ Z), Set.range h.left ⊆ U ↔ ∃ h' : T ⟶ V, h' ≫ i = h := by
  have hc : IsClosedImmersion U.ι := .of_isPreimmersion _ (by simpa using hU)
  refine ⟨Over.mk (U.ι ≫ Z.hom), Over.homMk U.ι rfl, inferInstanceAs (IsFinite (U.ι ≫ Z.hom)),
    inferInstanceAs (Etale (U.ι ≫ Z.hom)), ?_, fun T h => ?_⟩
  · have : Mono (Over.homMk U.ι rfl : Over.mk (U.ι ≫ Z.hom) ⟶ Z).left := inferInstanceAs (Mono U.ι)
    exact Over.mono_of_mono_left _
  · rw [FinEt.range_subset_iff_factors]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨Over.homMk t ?_, Over.OverMorphism.ext ht⟩
      show t ≫ U.ι ≫ Z.hom = T.hom
      rw [← Category.assoc, ht, Over.w h]
    · rintro ⟨t, ht⟩
      exact ⟨t.left, congrArg CommaMorphism.left ht⟩
end GlobalTheory.LevCover
