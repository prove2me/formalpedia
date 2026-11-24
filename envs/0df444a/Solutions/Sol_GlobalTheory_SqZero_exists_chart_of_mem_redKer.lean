-- Prove2me | solution 1 for GlobalTheory.SqZero.exists_chart_of_mem_redKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:27:43.636483+00:00
-- url     : https://prove2.me/submissions/cc51eb60-6988-442b-9c2f-af490a71b4bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Theorems.Thm_GlobalTheory_SqZero_nil_of_sq
import Theorems.Thm_GlobalTheory_SqZero_mem_redKer
import Theorems.Thm_GlobalTheory_SqZero_exists_chart_pt_of_nil
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
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
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  {A A' A₀ : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  [CommRing A₀] [Algebra R A₀]
variable {G}
namespace GlobalTheory.SqZero
theorem _root_.solution {B : Type} [CommRing B] [Algebra R B] (j : sp B ⟶ G)
    [IsOpenImmersion j.left] (u : B →ₐ[R] A) (hu : spMap u ≫ j = 1) {J : Ideal A} (hJ : J ^ 2 = ⊥)
    {y : sp A ⟶ G} (hy : y ∈ redKer G J) :
    ∃ φ : B →ₐ[R] A, y = spMap φ ≫ j ∧ ∀ b, φ b - u b ∈ J := by
  obtain ⟨φ, h1, h2⟩ := exists_chart_pt_of_nil j (Ideal.Quotient.mkₐ R J)
    (Ideal.Quotient.mkₐ_surjective R J) (nil_of_sq hJ) y ((Ideal.Quotient.mkₐ R J).comp u)
    (by rw [mem_redKer.1 hy, ← spMap_comp, Category.assoc, hu, comp_one'])
  exact ⟨φ, h1, fun b => Ideal.Quotient.eq.1 (AlgHom.congr_fun h2 b)⟩
end GlobalTheory.SqZero
