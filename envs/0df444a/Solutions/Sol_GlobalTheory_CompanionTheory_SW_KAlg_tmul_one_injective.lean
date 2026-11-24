-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.KAlg.tmul_one_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:26:39.845601+00:00
-- url     : https://prove2.me/submissions/15a71788-4052-47d9-9b65-72e57b5dfb4f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_KAlg_coord_inj

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.KAlg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R : Type} [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.KAlg
theorem _root_.solution (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ) :
    Function.Injective (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E) := by
  intro p q h
  have h' : p ⊗ₜ[F] (1 : E) + (0 : R) ⊗ₜ[F] δ = q ⊗ₜ[F] (1 : E) + (0 : R) ⊗ₜ[F] δ := by
    simpa using h
  exact (coord_inj b hb0 hb1 h').1
end GlobalTheory.CompanionTheory.SW.KAlg
