-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HermRep.sig_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:24:12.110717+00:00
-- url     : https://prove2.me/submissions/35d38b7f-3316-4729-a02e-89d9d8fa7a32

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_EqIdOfFixed
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermRep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
namespace GlobalTheory.CompanionTheory.SW.HermRep
theorem _root_.solution (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]
end GlobalTheory.CompanionTheory.SW.HermRep
