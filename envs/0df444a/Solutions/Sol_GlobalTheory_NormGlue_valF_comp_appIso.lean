-- Prove2me | solution 1 for GlobalTheory.NormGlue.valF_comp_appIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:27:59.585016+00:00
-- url     : https://prove2.me/submissions/3790e92d-c206-4a9f-a159-df10cdde0e18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_CompanionTheory
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_RegularOfBoundedAtPadicAlgClPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleOfNormOneGenerators
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


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
theorem _root_.solution {F : Type} [Field F] {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (V : Y.Opens) (u : Γ(Y, V)) (y₀ : Sp F ⟶ Y) :
    valF (y₀ ≫ f) (f ''ᵁ V) ((f.appIso V).inv.hom u) = valF y₀ V u := by
  have e : (y₀ ≫ f) ⁻¹ᵁ (f ''ᵁ V) = y₀ ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]
  unfold valF
  by_cases h : ⊤ ≤ y₀ ⁻¹ᵁ V
  · rw [dif_pos h, dif_pos (e ▸ h)]
    congr 1
    rw [← Scheme.Hom.appLE_comp_appLE y₀ f (f ''ᵁ V) V ⊤ (f.preimage_image_eq V).ge h,
      ← Scheme.Hom.appIso_hom']
    change (y₀.appLE V ⊤ h).hom (((f.appIso V).inv ≫ (f.appIso V).hom).hom u) = _
    rw [Iso.inv_hom_id]
    rfl
  · rw [dif_neg h, dif_neg (e ▸ h)]
end GlobalTheory.NormGlue
