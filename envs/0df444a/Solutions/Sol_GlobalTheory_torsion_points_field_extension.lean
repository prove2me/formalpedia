-- Prove2me | solution 1 for GlobalTheory.torsion_points_field_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:58:11.33562+00:00
-- url     : https://prove2.me/submissions/d22b0f3a-3287-494d-98fe-9f0a06e6dbc8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionPointsFieldExtension
import Theorems.Thm_GlobalTheory_TorsionFieldExt_comp_injective
import Theorems.Thm_GlobalTheory_TorsionFieldExt_exists_of_isAlgClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open TorsionFieldExt
namespace GlobalTheory
theorem _root_.solution : Out.Laws → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] (i : K →+* Ω) (x : Sp K ⟶ S), Function.Injective (fun y : Over.mk x ⟶ P.A => (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ∧ ∀ (n : ℕ) (z : Over.mk (spMap i ≫ x) ⟶ P.A), (n : K) ≠ 0 → z ^ n = 1 → ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y = z := by
  intro hL S P K Ω _ _ _ i x
  refine ⟨comp_injective _ _, fun n z hn hz => ?_⟩
  let j : Ω →+* AlgebraicClosure Ω := algebraMap _ _
  let v : Over.mk (spMap j ≫ spMap i ≫ x) ⟶ Over.mk (spMap i ≫ x) := Over.homMk (spMap j) rfl
  have hn' : (n : AlgebraicClosure Ω) ≠ 0 := by
    rw [← map_natCast (j.comp i)]
    exact (map_ne_zero _).2 hn
  obtain ⟨y, hy, e⟩ := exists_of_isAlgClosed hL P
    (v ≫ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x)) hn hn' (v ≫ z)
    (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
  exact ⟨y, hy, comp_injective v _ ((Category.assoc _ _ _).symm.trans e)⟩
end GlobalTheory
