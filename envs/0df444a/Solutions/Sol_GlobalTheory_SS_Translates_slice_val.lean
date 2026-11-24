-- Prove2me | solution 1 for GlobalTheory.SS.Translates.slice_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:56:03.739413+00:00
-- url     : https://prove2.me/submissions/123e9863-915b-4eea-911c-0a3d853df580

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatible
import Theorems.Thm_GlobalTheory_SS_Translates_val_eq
import Theorems.Thm_GlobalTheory_SS_Translates_dense_j
import Theorems.Thm_GlobalTheory_SS_Translates_pj_snd

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
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Translates
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
namespace GlobalTheory.SS.Translates
theorem _root_.solution [IsDomain R] [IsFractionRing R K] (M : Model R A) (σ : M.Y ⟶ M.Y ⊗ M.Y) (σ' : A ⟶ A ⊗ A)
    (hσ : M.j ≫ σ.left = σ'.left ≫ pj M M) (F : A ⊗ A ⟶ A ⊗ A) {f : A ⟶ A} (hf : σ' ≫ F ≫ snd A A = f)
    {X X' : Scheme.{0}} {i g : X ⟶ M.Y.left} {I G : X' ⟶ (M.Y ⊗ M.Y).left} [IsOpenImmersion i] [IsOpenImmersion I]
    (h : Ext M M f i g) (h' : Ext (M.prod M) (M.prod M) F I G) {o : X} {o' : X'} (e : I o' = σ.left (i o)) :
    g o = (snd M.Y M.Y).left (G o') := by
  have := M.sep
  have h1 : G ≫ (M.Y ⊗ M.Y).hom = I ≫ (M.Y ⊗ M.Y).hom := h'.1
  have h2 : ∀ (T : Scheme.{0}) (t : T ⟶ X') (a : T ⟶ (A ⊗ A).left), t ≫ I = a ≫ pj M M →
    t ≫ G = a ≫ F.left ≫ pj M M := h'.2
  refine val_eq M.j (dense_j M (i o)) (𝟙 _) σ.left i I g (G ≫ (snd M.Y M.Y).left) M.Y.hom M.Y.hom (M.Y ⊗ M.Y).hom
    h.1 ?_ ?_ ?_ rfl e
  · rw [Category.assoc, ← h1, Over.w]
  · rw [Category.id_comp, Over.w]
  · intro T a t₁ t₂ e₁ e₂
    rw [h.2 T t₁ a (by simpa using e₁), ← Category.assoc t₂, h2 T t₂ (a ≫ σ'.left) (by rw [e₂, hσ, Category.assoc]), ← hf]
    simp only [Category.assoc, Over.comp_left, pj_snd]
end GlobalTheory.SS.Translates
