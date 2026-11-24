-- Prove2me | solution 1 for GlobalTheory.T.exists_real_flow_adelic_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:52:03.959958+00:00
-- url     : https://prove2.me/submissions/1dc05cec-0faa-46b4-804b-622984d3c49a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsRealFlowAdelicUnits
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsRealFlowAdelicUnitsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Flow_exists_flow


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Flow.exists_flow | exact GlobalTheory.CompanionTheory.SW.Flow.exists_flow | (intros; apply GlobalTheory.CompanionTheory.SW.Flow.exists_flow <;> assumption)
end _root_.GlobalTheory.T
