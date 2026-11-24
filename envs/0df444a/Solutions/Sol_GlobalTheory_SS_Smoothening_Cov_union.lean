-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.Cov.union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:21:58.548903+00:00
-- url     : https://prove2.me/submissions/fd5502de-24b0-4e0a-82e8-a667a117be4f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterizationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Smoothening
variable {R K B C : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
namespace GlobalTheory.SS.Smoothening
namespace Cov
theorem _root_.solution {E E₁ E₂ : Pts R B} (h₁ : Cov K E₁) (h₂ : Cov K E₂)
    (h : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → E₁ R' a ∨ E₂ R' a) : Cov K E := by
  obtain ⟨l₁, p₁, q₁⟩ := h₁
  obtain ⟨l₂, p₂, q₂⟩ := h₂
  refine ⟨l₁ ++ l₂, fun x hx => (List.mem_append.1 hx).elim (p₁ x) (p₂ x), fun R' _ _ a ha => ?_⟩
  rcases h R' a ha with h | h
  · obtain ⟨x, hx, r⟩ := q₁ R' a h
    exact ⟨x, List.mem_append_left _ hx, r⟩
  · obtain ⟨x, hx, r⟩ := q₂ R' a h
    exact ⟨x, List.mem_append_right _ hx, r⟩
end Cov
end GlobalTheory.SS.Smoothening
