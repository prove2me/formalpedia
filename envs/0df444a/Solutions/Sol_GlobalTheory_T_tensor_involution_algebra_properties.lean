-- Prove2me | solution 1 for GlobalTheory.T.tensor_involution_algebra_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:08:12.801816+00:00
-- url     : https://prove2.me/submissions/6ea314ab-e895-4d41-a4ba-71be2ad72cbb

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraPropertiesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_KAlg_algebra_tensor_invol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R], IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsUnit (2 : R ⊗[F] E) ∧ (∀ y, sigR R σ (sigR R σ y) = y) ∧ (∃ δ : R ⊗[F] E, IsUnit δ ∧ sigR R σ δ = -δ) ∧ (∀ y : R ⊗[F] E, sigR R σ y = y → ∃ r : R, y = r ⊗ₜ[F] (1 : E)) ∧ ∀ r : R, IsUnit (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) ↔ IsUnit r := by
  first | exact @GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol | exact GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol | (intros; apply GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol <;> assumption)
end _root_.GlobalTheory.T
