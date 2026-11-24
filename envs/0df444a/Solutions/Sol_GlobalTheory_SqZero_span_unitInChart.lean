-- Prove2me | solution 1 for GlobalTheory.SqZero.span_unitInChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:46:33.43028+00:00
-- url     : https://prove2.me/submissions/5b51c845-6e72-4860-b5d4-c49b00ea16a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Theorems.Thm_GlobalTheory_SqZero_exists_local_chart
import Theorems.Thm_GlobalTheory_SqZero_isAway_awayHom
import Theorems.Thm_GlobalTheory_SqZero_span_eq_top_of_forall_maximal
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
theorem _root_.solution :
    Ideal.span {f : A | UnitInChart G (Localization.Away f)} = ⊤ := by
  refine span_eq_top_of_forall_maximal fun m hm => ?_
  obtain ⟨f, hf, B, _, _, j, hj, h⟩ := exists_local_chart (1 : sp A ⟶ G) m hm.isPrime
  obtain ⟨u, hu⟩ := h _ (awayHom R f) (isAway_awayHom f).unit
  exact ⟨f, ⟨B, _, _, j, u, hj, by rw [← hu, comp_one']⟩, hf⟩
end GlobalTheory.SqZero
