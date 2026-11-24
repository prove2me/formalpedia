-- Prove2me | solution 1 for GlobalTheory.SqZero.IsAway.swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:42:36.744803+00:00
-- url     : https://prove2.me/submissions/108159fd-74b7-41e6-bd2b-79accbcaa8f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Theorems.Thm_GlobalTheory_SqZero_IsAway_cancel
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
variable {S S' S'' T : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing S''] [Algebra R S''] [CommRing T] [Algebra R T]
open GlobalTheory.SqZero.IsAway
variable {ρ : S →ₐ[R] S'} {g : S}
namespace GlobalTheory.SqZero.IsAway
theorem _root_.solution (h : IsAway ρ g) {ρ₂ : S →ₐ[R] S''} {g' : S} (h₂ : IsAway ρ₂ g')
    {ν : S' →ₐ[R] T} {ξ : S'' →ₐ[R] T} (e : ν.comp ρ = ξ.comp ρ₂) (hξ : IsAway ξ (ρ₂ g)) :
    IsAway ν (ρ g') := by
  refine h.cancel ?_
  rw [e, mul_comm]
  exact h₂.comp hξ
end GlobalTheory.SqZero.IsAway
