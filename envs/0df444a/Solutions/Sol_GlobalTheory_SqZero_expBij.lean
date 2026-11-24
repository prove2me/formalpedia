-- Prove2me | solution 1 for GlobalTheory.SqZero.expBij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:32:58.599514+00:00
-- url     : https://prove2.me/submissions/c0bea82f-7daf-4ead-ab62-0a2452ada346

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Theorems.Thm_GlobalTheory_SqZero_isLieBasisOver_self
import Theorems.Thm_GlobalTheory_SqZero_IsLieBasisOver_away
import Theorems.Thm_GlobalTheory_SqZero_expBij_of_unitInChart
import Theorems.Thm_GlobalTheory_SqZero_expBij_of_span
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_isAway_awayHom
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
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {S S' A : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing A] [Algebra R A]
variable {v : Fin n → (epsR R ⟶ G)}
variable [Smooth G.hom]
variable (A)
namespace GlobalTheory.SqZero
theorem _root_.solution (hv : IsLieBasis v) : ExpBij A v := by
  refine expBij_of_span
    (s := Algebra.ofId R A '' {g : R | UnitInChart G (Localization.Away g)}) ?_ ?_
  · rw [← Ideal.map_span, span_unitInChart, Ideal.map_top]
  · rintro _ ⟨g, hg, rfl⟩ T _ _ φ hφ
    have hρ := isAway_awayHom (R := R) g
    obtain ⟨α, -⟩ := hρ.lift (φ.comp (Algebra.ofId R A)) hφ
    exact expBij_of_unitInChart hv.1 hg ((isLieBasisOver_self hv).away hv.1 hρ) α
end GlobalTheory.SqZero
