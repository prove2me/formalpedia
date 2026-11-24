-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SizeInt.continuous_ainfEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:53.851893+00:00
-- url     : https://prove2.me/submissions/b7290d31-7740-4b9b-a26c-42ac7e183f5c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SizeFunctionRapidDecayIntegrable
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeInt_continuous_compReal

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SizeInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable {d : ℕ} (hF : IsTotallyReal F) (b : Module.Basis (Fin d) F E)
namespace GlobalTheory.CompanionTheory.SW.SizeInt
theorem _root_.solution : Continuous (ainfEquiv hF) :=
  continuous_pi fun v => (continuous_compReal hF v).comp (continuous_apply (A := fun v : InfinitePlace F => v.Completion) v)
end GlobalTheory.CompanionTheory.SW.SizeInt
