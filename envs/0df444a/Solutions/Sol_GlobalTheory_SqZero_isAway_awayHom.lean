-- Prove2me | solution 1 for GlobalTheory.SqZero.isAway_awayHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:49.089467+00:00
-- url     : https://prove2.me/submissions/11bb716c-4317-4781-9687-a48d1ee9cb2d

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
variable {S S' S'' T : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing S''] [Algebra R S''] [CommRing T] [Algebra R T]
namespace GlobalTheory.SqZero
theorem _root_.solution (g : S) : IsAway (awayHom R g) g :=
  (isAway_iff _ _).2 ⟨IsLocalization.Away.algebraMap_isUnit g,
    fun z => IsLocalization.Away.surj g z, fun a ha => by
      obtain ⟨N, hN⟩ := IsLocalization.Away.exists_of_eq (S := Localization.Away g) g (a := a)
        (b := 0) (by rw [map_zero]; exact ha)
      exact ⟨N, by simpa using hN⟩⟩
end GlobalTheory.SqZero
