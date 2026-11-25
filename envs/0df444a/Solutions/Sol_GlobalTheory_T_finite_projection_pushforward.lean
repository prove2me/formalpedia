-- Prove2me | solution 1 for GlobalTheory.T.finite_projection_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:19:25.826799+00:00
-- url     : https://prove2.me/submissions/af5e1e6e-bf2a-4eaf-94a8-aa8a83c92453

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProjectionPushforward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProjectionPushforwardStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_irreducibleGerm_contains_centredDiscCover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : FiniteGermProjectionOpenAt.Statement → IrreducibleGermPrimitiveForm.Statement → PrimitiveFormSheetedOffDiscriminant.Statement → UnbranchedProperCountConstant.Statement → ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), IsAnalyticNear Y w → GermIrreducibleAt Y w → (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) → (∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) → ∀ᶠ y in 𝓝 (A w), h y = 0) → ∃ (Y' : Set (σ → ℂ)) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ), Y' ⊆ Y ∧ IsCentredDiscCover Y' w p ρ N := by
  first | exact @GlobalTheory.CompanionTheory.ComplexSets.irreducibleGerm_contains_centredDiscCover | exact GlobalTheory.CompanionTheory.ComplexSets.irreducibleGerm_contains_centredDiscCover | (intros; apply GlobalTheory.CompanionTheory.ComplexSets.irreducibleGerm_contains_centredDiscCover <;> assumption)
end _root_.GlobalTheory.T
