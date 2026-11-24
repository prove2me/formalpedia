-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramAlg.sigma_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:21:19.6817+00:00
-- url     : https://prove2.me/submissions/05f064cf-d9cf-46f8-bb5a-2267ad6d8676

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramAlg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.GramAlg
theorem _root_.solution [NumberField F] [NumberField E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (x : E) :
    σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hσ.2.2.2 τ, hσ.2.2.2 τ, star_star]
end GlobalTheory.CompanionTheory.SW.GramAlg
