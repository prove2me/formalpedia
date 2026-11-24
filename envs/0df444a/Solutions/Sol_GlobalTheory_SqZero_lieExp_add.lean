-- Prove2me | solution 1 for GlobalTheory.SqZero.lieExp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:07:27.947591+00:00
-- url     : https://prove2.me/submissions/796e998f-0b5c-4d1d-972b-3a0a75228085

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Theorems.Thm_GlobalTheory_SqZero_epsTo_add_comp
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
variable [IsCommMonObj G] {n : ℕ}
variable {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i))
include hv
namespace GlobalTheory.SqZero
theorem _root_.solution (c c' : Fin n → A) (hc : ∀ i, c i * c i = 0) (hc' : ∀ i, c' i * c' i = 0)
    (hcc : ∀ i, c i * c' i = 0) (h : ∀ i, (c i + c' i) * (c i + c' i) = 0) :
    lieExp v (fun i => c i + c' i) h = lieExp v c hc * lieExp v c' hc' := by
  rw [lieExp, lieExp, lieExp, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => epsTo_add_comp ((isTan_iff _).2 (hv i)) _ _ _ _ (hcc i) _
end GlobalTheory.SqZero
