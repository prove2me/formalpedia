-- Prove2me | solution 1 for GlobalTheory.LevCover.range_subset_of_geom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:03.5208+00:00
-- url     : https://prove2.me/submissions/55c8d2e7-9d9e-4299-97df-8bbfc089d905

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom
import Theorems.Thm_GlobalTheory_FinEt_exists_algClosed_point


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
theorem _root_.solution {T Z : Over S} (h : T ⟶ Z) (U : Set Z.left)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (y : Over.mk x ⟶ T), Set.range (y ≫ h).left ⊆ U) :
    Set.range h.left ⊆ U := by
  rintro _ ⟨t, rfl⟩
  obtain ⟨k, _, _, a, ha⟩ := FinEt.exists_algClosed_point T.left t
  obtain ⟨p, rfl⟩ : t ∈ Set.range a := by rw [ha]; rfl
  exact H k (a ≫ T.hom) (Over.homMk a rfl) ⟨p, by simp⟩
end GlobalTheory.LevCover
