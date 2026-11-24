-- Prove2me | solution 1 for GlobalTheory.SqZero.exists_chart_pt_of_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:12:31.303805+00:00
-- url     : https://prove2.me/submissions/ac8da29d-444a-4dc3-a402-e3f5d2538c62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Theorems.Thm_GlobalTheory_SqZero_chart_inj
import Theorems.Thm_GlobalTheory_SqZero_exists_chart_pt
import Theorems.Thm_GlobalTheory_SqZero_spMap_surjective
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
theorem _root_.solution (j : sp B ⟶ X) [IsOpenImmersion j.left] (q : A →ₐ[R] A₀)
    (hq : Function.Surjective q) (hn : ∀ a, q a = 0 → IsNilpotent a) (y : sp A ⟶ X)
    (φ₀ : B →ₐ[R] A₀) (h : spMap q ≫ y = spMap φ₀ ≫ j) :
    ∃ φ : B →ₐ[R] A, y = spMap φ ≫ j ∧ q.comp φ = φ₀ := by
  obtain ⟨φ, rfl⟩ := exists_chart_pt j y (by
    rintro _ ⟨p, rfl⟩
    obtain ⟨p₀, rfl⟩ := spMap_surjective q hq hn p
    refine ⟨(spMap φ₀).left p₀, ?_⟩
    have := congrArg (fun z : sp A₀ ⟶ X => z.left p₀) h
    simpa using this.symm)
  rw [← Category.assoc, spMap_comp] at h
  exact ⟨φ, rfl, chart_inj j h⟩
end GlobalTheory.SqZero
