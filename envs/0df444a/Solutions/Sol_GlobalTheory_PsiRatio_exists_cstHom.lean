-- Prove2me | solution 1 for GlobalTheory.PsiRatio.exists_cstHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:09:51.711603+00:00
-- url     : https://prove2.me/submissions/a46c37d7-0bef-467b-b0f8-f8f26c9a1c4b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulPullSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_JKAppTopInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PsiScalarEqExpansionCoefRatio
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
open GlobalTheory GlobalTheory.PsiRatio
namespace GlobalTheory.PsiRatio
theorem _root_.solution {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) :
    ∃ φ : F →+* Z.presheaf.stalk z, (∀ c, cst p z c = φ c) ∧ ∀ c, gs (𝟙 _) z ⊤ (scal p c) = φ c := by
  refine ⟨(Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp ((p.app ⊤).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom), fun c => gs_eq p z ⊤ trivial _, fun c => ?_⟩
  exact gs_eq (𝟙 _) z ⊤ trivial _
end GlobalTheory.PsiRatio
