-- Prove2me | solution 1 for GlobalTheory.SS.GlueCompat.glue_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:11.52107+00:00
-- url     : https://prove2.me/submissions/fa6c0432-d729-4db3-9d02-f46698c80c2c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModels
import Theorems.Thm_GlobalTheory_SS_GlueCompat_exists_union
import Theorems.Thm_GlobalTheory_SS_GlueCompat_compat_of_cover
import Theorems.Thm_GlobalTheory_SS_Model_le_refl


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
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}
variable [IsDomain R] [IsFractionRing R K]
namespace GlobalTheory.SS.GlueCompat
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (n : ℕ) (M : Fin (n + 1) → Model R A), (∀ i j, Compat (M i) (M j)) → ∃ G : Model R A, (∀ i, (M i).Le G) ∧ (∀ y : G.Y.left, ∃ (i : Fin (n + 1)) (g : (M i).Y ⟶ G.Y), IsOpenImmersion g.left ∧ (M i).j ≫ g.left = G.j ∧ y ∈ Set.range g.left) ∧ ∀ N : Model R A, (∀ i, Compat N (M i)) → Compat N G := by
  intro R K _ _ _ _ _ _ A n
  induction n with
  | zero =>
    intro M _
    refine ⟨M 0, fun i => ?_, fun y => ⟨0, 𝟙 _, ?_, by simp, by simp⟩, fun N h => h 0⟩
    · obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
      exact Model.le_refl _
    · rw [Over.id_left]; infer_instance
  | succ n ih =>
    intro M hM
    obtain ⟨G₀, le₀, cov₀, comp₀⟩ := ih (fun i => M i.succ) (fun i j => hM _ _)
    obtain ⟨G, g₁, g₂, o₁, o₂, j₁, j₂, cov⟩ := exists_union (comp₀ (M 0) (fun i => hM _ _))
    refine ⟨G, fun i => ?_, fun y => ?_, fun N hN => compat_of_cover g₁ g₂ j₁ j₂ cov (hN 0) (comp₀ N fun i => hN _)⟩
    · refine Fin.cases ⟨g₁, o₁, j₁⟩ (fun i => (le₀ i).trans ⟨g₂, o₂, j₂⟩) i
    · rcases cov y with hy | ⟨x, rfl⟩
      · exact ⟨0, g₁, o₁, j₁, hy⟩
      · obtain ⟨i, g, og, jg, z, rfl⟩ := cov₀ x
        refine ⟨i.succ, g ≫ g₂, ?_, ?_, z, ?_⟩
        · rw [Over.comp_left]; infer_instance
        · rw [Over.comp_left, reassoc_of% jg, j₂]
        · rw [Over.comp_left, Scheme.Hom.comp_apply]
end GlobalTheory.SS.GlueCompat
