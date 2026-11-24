-- Prove2me | solution 1 for GlobalTheory.SS.GlueCompat.closed_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:34:16.035868+00:00
-- url     : https://prove2.me/submissions/94d12957-0c12-4806-bd2a-d395d2251267

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModels
import Theorems.Thm_GlobalTheory_SS_GlueCompat_target_two
import Theorems.Thm_GlobalTheory_SS_GlueCompat_pb_snd

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GlueCompat
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.SS.GlueCompat
theorem _root_.solution {S : Scheme.{0}} {X N G M₁ M₂ W₁ W₂ : Over S} (p : X ⟶ N) (q : X ⟶ G) {g₁ : M₁ ⟶ G} {g₂ : M₂ ⟶ G}
    [IsOpenImmersion g₁.left] [IsOpenImmersion g₂.left]
    (hc : ∀ x : G.left, x ∈ Set.range g₁.left ∨ x ∈ Set.range g₂.left)
    {a₁ : W₁ ⟶ X} {b₁ : W₁ ⟶ M₁} {a₂ : W₂ ⟶ X} {b₂ : W₂ ⟶ M₂}
    (h₁ : IsPullback a₁.left b₁.left q.left g₁.left) (h₂ : IsPullback a₂.left b₂.left q.left g₂.left)
    (c₁ : IsClosedImmersion (lift (a₁ ≫ p) b₁).left) (c₂ : IsClosedImmersion (lift (a₂ ≫ p) b₂).left) :
    IsClosedImmersion (lift p q).left := by
  have key : ∀ {M W : Over S} {g : M ⟶ G} {a : W ⟶ X} {b : W ⟶ M}, IsPullback a.left b.left q.left g.left →
      IsPullback a.left (lift (a ≫ p) b).left (lift p q).left (N ◁ g).left := by
    intro M W g a b h
    have e : a ≫ q = b ≫ g := Over.OverMorphism.ext h.w
    refine IsPullback.of_bot ?_ ?_ (pb_snd N g)
    · rwa [← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
    · rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      ext <;> simp [e]
  have : IsOpenImmersion (N ◁ g₁).left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (pb_snd N g₁).flip ‹_›
  have : IsOpenImmersion (N ◁ g₂).left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (pb_snd N g₂).flip ‹_›
  refine target_two @IsClosedImmersion ?_ (key h₁) (key h₂) c₁ c₂
  intro z
  rcases hc ((snd N G).left z) with ⟨y, hy⟩ | ⟨y, hy⟩
  · obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback (pb_snd N g₁) z y hy.symm
    exact Or.inl ⟨w, hw⟩
  · obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback (pb_snd N g₂) z y hy.symm
    exact Or.inr ⟨w, hw⟩
end GlobalTheory.SS.GlueCompat
