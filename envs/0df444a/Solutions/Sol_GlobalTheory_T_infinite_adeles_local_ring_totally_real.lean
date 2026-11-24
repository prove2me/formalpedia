-- Prove2me | solution 1 for GlobalTheory.T.infinite_adeles_local_ring_totally_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:12:46.529922+00:00
-- url     : https://prove2.me/submissions/47cf4ed3-6b96-41fd-93aa-942e07329b83

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_isLocR_Ainf


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → IsLocR (Ainf F) := by
  first | exact @GlobalTheory.CompanionTheory.SW.isLocR_Ainf | exact GlobalTheory.CompanionTheory.SW.isLocR_Ainf | (intros; apply GlobalTheory.CompanionTheory.SW.isLocR_Ainf <;> assumption)
end _root_.GlobalTheory.T
