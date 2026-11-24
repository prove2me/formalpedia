-- Prove2me | solution 1 for GlobalTheory.SqZero.chart_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:09.174843+00:00
-- url     : https://prove2.me/submissions/068a55a0-6ea4-426b-b64a-be85cf58908f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
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
theorem _root_.solution (j : sp B ⟶ X) [IsOpenImmersion j.left] {φ φ' : B →ₐ[R] A}
    (h : spMap φ ≫ j = spMap φ' ≫ j) : φ = φ' := by
  have h1 := congrArg CommaMorphism.left h
  simp only [Over.comp_left, cancel_mono, spMap_left] at h1
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective h1))
end GlobalTheory.SqZero
