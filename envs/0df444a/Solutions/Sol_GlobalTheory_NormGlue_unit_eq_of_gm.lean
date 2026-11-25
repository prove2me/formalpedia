-- Prove2me | solution 1 for GlobalTheory.NormGlue.unit_eq_of_gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:14.123604+00:00
-- url     : https://prove2.me/submissions/c98c0f2a-b0a2-46db-bf4b-6d32c91837de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_CompanionTheory
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_RegularOfBoundedAtPadicAlgClPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleOfNormOneGenerators
import Theorems.Thm_GlobalTheory_NormGlue_appLE_injective
import Theorems.Thm_GlobalTheory_NormGlue_preimage_nonempty
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory
open GlobalTheory.NormGlue
namespace GlobalTheory.NormGlue
theorem _root_.solution {X Y : Scheme.{0}} [IsIntegral X] (f : Y ⟶ X) [IsOpenImmersion f] (ξ : Y)
    (hξ : ∀ O : Y.Opens, (O : Set Y).Nonempty → ξ ∈ O) {U : X.Opens} {u u' : Γ(X, U)ˣ}
    (h : f ξ ∈ U → gm f ξ U u = gm f ξ U u') : u = u' := by
  by_cases hU : (U : Set X).Nonempty
  · haveI : Nonempty Y := ⟨ξ⟩
    haveI : IsIntegral Y := isIntegral_of_isOpenImmersion f
    have hne := preimage_nonempty f ξ hU
    have hm : f ξ ∈ U := hξ _ hne
    have e := congrArg Units.val (h hm)
    rw [gm_val f ξ U hm, gm_val f ξ U hm] at e
    have e' := germ_injective_of_isIntegral Y (U := f ⁻¹ᵁ U) ξ hm e
    apply Units.ext
    apply appLE_injective f U (f ⁻¹ᵁ U) le_rfl hne
    rw [Scheme.Hom.appLE_eq_app]
    exact e'
  · exact unit_ext fun x hx => (hU ⟨x, hx⟩).elim
end GlobalTheory.NormGlue
