-- Prove2me | solution 1 for GlobalTheory.SS.FinUnion.mem_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:54:56.343262+00:00
-- url     : https://prove2.me/submissions/33063209-9264-4a19-bd2a-023a6f6fafa7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModelsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnionTranslates

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FinUnion
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.FinUnion
theorem _root_.solution {S : Scheme.{0}} {W N G U : Over S} (g : W ⟶ N) (h : W ⟶ G) [IsClosedImmersion (lift g h).left]
    (q : U ⟶ N) (φ : U ⟶ G) {T : Scheme.{0}} (t : T ⟶ U.left) (ht : DenseRange t) (r : T ⟶ W.left)
    (h1 : t ≫ q.left = r ≫ g.left) (h2 : t ≫ φ.left = r ≫ h.left) (z : U.left) :
    ∃ w, g.left w = q.left z ∧ h.left w = φ.left z := by
  have e : t ≫ (lift q φ).left = r ≫ (lift g h).left := by
    apply pullback.hom_ext
    · change (t ≫ (lift q φ).left) ≫ (fst N G).left = (r ≫ (lift g h).left) ≫ (fst N G).left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, h1]
    · change (t ≫ (lift q φ).left) ≫ (snd N G).left = (r ≫ (lift g h).left) ≫ (snd N G).left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, h2]
  have hc : IsClosed ((lift q φ).left ⁻¹' Set.range (lift g h).left) :=
    (lift g h).left.isClosedEmbedding.isClosed_range.preimage (lift q φ).left.continuous
  have hs : Set.range t ⊆ (lift q φ).left ⁻¹' Set.range (lift g h).left := by
    rintro _ ⟨x, rfl⟩
    exact ⟨r x, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e]⟩
  obtain ⟨w, hw⟩ := hc.closure_subset_iff.2 hs (ht z)
  refine ⟨w, ?_, ?_⟩
  · have := congrArg (fst N G).left hw
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst] at this
  · have := congrArg (snd N G).left hw
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd] at this
end GlobalTheory.SS.FinUnion
