-- Prove2me | solution 1 for GlobalTheory.NormGlue.appLE_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:23:01.548067+00:00
-- url     : https://prove2.me/submissions/923b6450-d213-49a1-8009-98db25cf4cc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_CompanionTheory
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_RegularOfBoundedAtPadicAlgClPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleOfNormOneGenerators
import Theorems.Thm_GlobalTheory_NormGlue_appLE_eq_appIso
import Theorems.Thm_GlobalTheory_NormGlue_image_le
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


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
theorem _root_.solution {X Y : Scheme.{0}} [IsIntegral X] (f : Y ⟶ X) [IsOpenImmersion f]
    (W : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ W) (hV : (V : Set Y).Nonempty) :
    Function.Injective (f.appLE W V h).hom := by
  intro a b hab
  rw [appLE_eq_appIso f W V h (image_le f h), appLE_eq_appIso f W V h (image_le f h)] at hab
  have h1 := (f.appIso V).commRingCatIsoToRingEquiv.injective hab
  obtain ⟨x, hx⟩ := hV
  haveI : Nonempty (f ''ᵁ V) := ⟨⟨f x, x, hx, rfl⟩⟩
  exact map_injective_of_isIntegral X (homOfLE (image_le f h)) h1
end GlobalTheory.NormGlue
