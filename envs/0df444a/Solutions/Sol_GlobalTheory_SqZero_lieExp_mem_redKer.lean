-- Prove2me | solution 1 for GlobalTheory.SqZero.lieExp_mem_redKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:31.081895+00:00
-- url     : https://prove2.me/submissions/803d59d9-f544-4b05-9b2a-344ae9df46ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Theorems.Thm_GlobalTheory_SqZero_epsTo_comp_mem_redKer
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
theorem _root_.solution {J : Ideal A} (c : Fin n → A) (hcJ : ∀ i, c i ∈ J)
    (hc : ∀ i, c i * c i = 0) : lieExp v c hc ∈ redKer G J :=
  prod_mem fun i _ => epsTo_comp_mem_redKer ((isTan_iff _).2 (hv i)) (hcJ i) _
end GlobalTheory.SqZero
