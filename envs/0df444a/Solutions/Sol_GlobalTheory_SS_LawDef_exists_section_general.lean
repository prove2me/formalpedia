-- Prove2me | solution 1 for GlobalTheory.SS.LawDef.exists_section_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:01:18.718858+00:00
-- url     : https://prove2.me/submissions/f361bd3f-d665-4084-87c8-8fb86624f29f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslate
import Theorems.Thm_GlobalTheory_SS_LawDef_sec_exists
import Theorems.Thm_GlobalTheory_SS_LawDef_exists_section

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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LawDef
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
variable [IsLocalRing R]
namespace GlobalTheory.SS.LawDef
theorem _root_.solution [IsDomain R] (hR : SH R K) {M : Model R A} (hi : M.Irr) {f : A ⟶ A}
    (hf : GenIso M M f) {V₁ V₂ : Set M.Y.left} (o₁ : IsOpen V₁) (o₂ : IsOpen V₂) (n₁ : (M.sp ∩ V₁).Nonempty)
    (n₂ : (M.sp ∩ V₂).Nonempty) :
    ∃ (s : 𝟙_ (Over (Sp R)) ⟶ M.Y), sp0 s ∈ V₁ ∧ ∀ p, Sec M p s → ∃ t, Sec M (p ≫ f) t ∧ sp0 t ∈ V₂ := by
  obtain ⟨w, hw, U, g, hwU, hg, ho⟩ := hf
  have key : ∀ u : U.toScheme, g u ∈ M.sp ↔ U.ι u ∈ M.sp := by
    intro u
    show M.Y.hom (g u) = _ ↔ M.Y.hom (U.ι u) = _
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg.1]
  obtain ⟨_, h1, ⟨u, rfl⟩, h2⟩ := hi.2 (Set.range g) V₂ g.isOpenEmbedding.isOpen_range o₂
    ⟨g ⟨w, hwU⟩, (key _).2 hw, _, rfl⟩ n₂
  have o₃ : IsOpen (U.ι '' (g ⁻¹' V₂)) := U.ι.isOpenEmbedding.isOpenMap _ (o₂.preimage g.continuous)
  obtain ⟨v, h3, h4⟩ := hi.2 V₁ _ o₁ o₃ n₁ ⟨U.ι u, (key _).1 h1, u, h2, rfl⟩
  obtain ⟨s, hs, u', hu', e⟩ := exists_section hR M (o₁.inter o₃).isLocallyClosed ⟨v, h4, h3⟩
  refine ⟨s, hs, fun p hp => ?_⟩
  obtain ⟨t, ht, e'⟩ := sec_exists hg hp u' e
  exact ⟨t, ht, e' ▸ hu'⟩
end GlobalTheory.SS.LawDef
