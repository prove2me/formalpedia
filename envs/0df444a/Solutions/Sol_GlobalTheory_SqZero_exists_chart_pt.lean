-- Prove2me | solution 1 for GlobalTheory.SqZero.exists_chart_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:15.367268+00:00
-- url     : https://prove2.me/submissions/42925f68-4951-4be8-b8fe-ef25c572b3d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_exists_spMap
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one')
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {X : Over (Spec (CommRingCat.of R))} {A A₀ B : Type} [CommRing A] [Algebra R A]
  [CommRing A₀] [Algebra R A₀] [CommRing B] [Algebra R B]
namespace GlobalTheory.SqZero
theorem _root_.solution (j : sp B ⟶ X) [IsOpenImmersion j.left] (y : sp A ⟶ X)
    (h : Set.range y.left ⊆ Set.range j.left) : ∃ φ : B →ₐ[R] A, y = spMap φ ≫ j := by
  obtain ⟨φ, hφ⟩ := exists_spMap (R := R) (A := A) (B := B)
    (Over.homMk (IsOpenImmersion.lift j.left y.left h) (by
      rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w]))
  refine ⟨φ, ?_⟩
  rw [← hφ]
  exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac j.left y.left h).symm
end GlobalTheory.SqZero
