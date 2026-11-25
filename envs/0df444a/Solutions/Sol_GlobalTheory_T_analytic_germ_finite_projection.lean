-- Prove2me | solution 1 for GlobalTheory.T.analytic_germ_finite_projection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:14.746818+00:00
-- url     : https://prove2.me/submissions/14784a5f-1a9d-4033-9462-18504f403a01

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnalyticGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnalyticGermFiniteProjectionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticGermSlice_exists_irreducible_slice


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
theorem _root_.solution : FiniteGermProjectionOpenAt.Statement → GermFiniteProjection.Statement → AnalyticGermComponents.Statement → ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → GermIrreducibleAt X w → AccPt w (𝓟 X) → ∃ (Y W : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), W ∈ 𝓝 w ∧ Y ∩ W ⊆ X ∧ IsAnalyticNear Y w ∧ GermIrreducibleAt Y w ∧ (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) ∧ ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) → ∀ᶠ y in 𝓝 (A w), h y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.AnalyticGermSlice.exists_irreducible_slice | exact GlobalTheory.CompanionTheory.AnalyticGermSlice.exists_irreducible_slice | (intros; apply GlobalTheory.CompanionTheory.AnalyticGermSlice.exists_irreducible_slice <;> assumption)
end _root_.GlobalTheory.T
