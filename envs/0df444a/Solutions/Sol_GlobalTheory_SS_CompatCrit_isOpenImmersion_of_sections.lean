-- Prove2me | solution 1 for GlobalTheory.SS.CompatCrit.isOpenImmersion_of_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:24:38.445065+00:00
-- url     : https://prove2.me/submissions/0d7a1181-999c-46ae-851d-472b16054b5c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfSections
import Theorems.Thm_GlobalTheory_SS_CompatCrit_section_open

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.CompatCrit
namespace GlobalTheory.SS.CompatCrit
theorem _root_.solution {G X : Scheme.{0}} [IsReduced G] (p : G ⟶ X) [IsSeparated p]
    (h : ∀ x : G, ∃ (V : Scheme.{0}) (s : V ⟶ G), IsDominant s ∧ IsOpenImmersion (s ≫ p) ∧ x ∈ Set.range s) :
    IsOpenImmersion p := by
  refine IsOpenImmersion.of_forall_source_exists p (fun x y hxy => ?_) (fun x => ?_)
  · obtain ⟨V, s, _, _, u, rfl⟩ := h x
    obtain ⟨v, rfl⟩ := (section_open p s).2 y ⟨u, by rw [← hxy, Scheme.Hom.comp_apply]⟩
    have : u = v := (s ≫ p).isOpenEmbedding.injective (by simpa using hxy)
    rw [this]
  · obtain ⟨V, s, _, _, hx⟩ := h x
    exact ⟨V, s, (section_open p s).1, hx, inferInstance⟩
end GlobalTheory.SS.CompatCrit
