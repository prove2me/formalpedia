-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Flow.continuous_tmul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:18:49.263952+00:00
-- url     : https://prove2.me/submissions/0fdcac5b-0c2b-4952-9527-90e098b6c64c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TotallyRealContinuousEmbeddingInfiniteAdelesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsRealFlowAdelicUnits

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Flow
namespace GlobalTheory.CompanionTheory.SW.Flow
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Continuous (fun a : AF F => a ⊗ₜ[F] (1 : E)) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  let φ : AF F →ₗ[AF F] AF F ⊗[F] E :=
    (TensorProduct.AlgebraTensorModule.mk F (AF F) (AF F) E).flip (1 : E)
  exact IsModuleTopology.continuous_of_linearMap φ
end GlobalTheory.CompanionTheory.SW.Flow
