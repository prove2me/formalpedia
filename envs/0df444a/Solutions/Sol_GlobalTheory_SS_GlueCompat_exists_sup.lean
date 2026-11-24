-- Prove2me | solution 1 for GlobalTheory.SS.GlueCompat.exists_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:17:55.478416+00:00
-- url     : https://prove2.me/submissions/9c64ccf0-d874-4184-bd47-9312738ee29e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModels

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
theorem _root_.solution {S : Scheme.{0}} {N W₁ W₂ : Over S} (p₁ : W₁ ⟶ N) (p₂ : W₂ ⟶ N) [IsOpenImmersion p₁.left]
    [IsOpenImmersion p₂.left] : ∃ (X : Over S) (p : X ⟶ N) (a₁ : W₁ ⟶ X) (a₂ : W₂ ⟶ X), IsOpenImmersion p.left ∧
      a₁ ≫ p = p₁ ∧ a₂ ≫ p = p₂ ∧ ∀ x, x ∈ Set.range a₁.left ∨ x ∈ Set.range a₂.left := by
  let U : N.left.Opens := p₁.left.opensRange ⊔ p₂.left.opensRange
  let X : Over S := Over.mk (U.ι ≫ N.hom)
  let p : X ⟶ N := Over.homMk U.ι rfl
  have op : IsOpenImmersion p.left := inferInstanceAs (IsOpenImmersion U.ι)
  have mk : ∀ {W : Over S} (p' : W ⟶ N) [IsOpenImmersion p'.left], p'.left.opensRange ≤ U →
      ∃ a : W ⟶ X, a ≫ p = p' := by
    intro W p' _ hle
    have hr : Set.range p'.left ⊆ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hle
    refine ⟨Over.homMk (IsOpenImmersion.lift U.ι p'.left hr) ?_, Over.OverMorphism.ext ?_⟩
    · change _ ≫ U.ι ≫ N.hom = _
      rw [IsOpenImmersion.lift_fac_assoc, Over.w p']
    · exact IsOpenImmersion.lift_fac U.ι p'.left hr
  obtain ⟨a₁, e₁⟩ := mk p₁ le_sup_left
  obtain ⟨a₂, e₂⟩ := mk p₂ le_sup_right
  refine ⟨X, p, a₁, a₂, op, e₁, e₂, fun x => ?_⟩
  have hx : p.left x ∈ U := x.2
  rcases TopologicalSpace.Opens.mem_sup.1 hx with ⟨y, hy⟩ | ⟨y, hy⟩
  · refine Or.inl ⟨y, p.left.isOpenEmbedding.injective ?_⟩
    rw [← hy, ← e₁, Over.comp_left, Scheme.Hom.comp_apply]
  · refine Or.inr ⟨y, p.left.isOpenEmbedding.injective ?_⟩
    rw [← hy, ← e₂, Over.comp_left, Scheme.Hom.comp_apply]
end GlobalTheory.SS.GlueCompat
