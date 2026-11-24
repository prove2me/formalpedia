-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.ScalTrace.hermScal_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:10:48.942803+00:00
-- url     : https://prove2.me/submissions/88139cbc-026f-438c-9ea9-ca7864b81792

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ScalarHermitianTraceAndUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.ScalTrace
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.BB.ScalTrace
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (s : R) :
    (hermScal R σ s : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = algebraMap R (R ⊗[F] E) s := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  rfl
end GlobalTheory.CompanionTheory.SW.BB.ScalTrace
