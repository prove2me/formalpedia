-- Prove2me | solution 1 for GlobalTheory.exists_finite_isAbelianScheme_descends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:48.440533+00:00
-- url     : https://prove2.me/submissions/72657e9e-dbe9-4a8e-80b2-70f7c587e2e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteIsAbelianSchemeDescends
import Theorems.Thm_GlobalTheory_exists_finite_isAbelianScheme_range
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS GlobalTheory.FieldModel
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (B : Over (Sp Ω)) [GrpObj B], IsAbelianScheme B → ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (B₁ : Over (Sp L)) (_ : GrpObj B₁) (e : (Over.pullback (spMap (algebraMap L Ω))).obj B₁ ≅ B), IsAbelianScheme B₁ ∧ IsMonHom e.hom := by
  intro K Ω _ _ _ _ B _ hB
  obtain ⟨s, hs, h⟩ := exists_finite_isAbelianScheme_range B hB
  have := hs.to_subtype
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨B₁, g, φ, ab, gp⟩ := h _ (algebraMap (IntermediateField.adjoin K s) Ω)
    fun x hx => ⟨⟨x, IntermediateField.subset_adjoin K s hx⟩, rfl⟩
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback B₁ _) gp
  exact ⟨IntermediateField.adjoin K s, IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, B₁, g, e, ab, he⟩
end GlobalTheory
