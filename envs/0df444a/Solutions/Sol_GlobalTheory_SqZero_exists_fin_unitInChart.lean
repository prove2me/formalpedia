-- Prove2me | solution 1 for GlobalTheory.SqZero.exists_fin_unitInChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:52:43.339797+00:00
-- url     : https://prove2.me/submissions/cfffdce4-8394-402e-b3a2-273f2849002b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Theorems.Thm_GlobalTheory_SqZero_span_unitInChart
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
variable (G A)
namespace GlobalTheory.SqZero
theorem _root_.solution : ∃ (κ : Type) (_ : Finite κ) (s : κ → A),
    Ideal.span (Set.range s) = ⊤ ∧ ∀ k, UnitInChart G (Localization.Away (s k)) := by
  obtain ⟨s, hs, hspan⟩ := (Ideal.span_eq_top_iff_finite _).1 (span_unitInChart G A)
  exact ⟨s, inferInstance, Subtype.val, by rw [Subtype.range_coe_subtype]; exact hspan,
    fun k => hs k.2⟩
end GlobalTheory.SqZero
