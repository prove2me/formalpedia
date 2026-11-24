-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Iwasawa.idem_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:24:19.284129+00:00
-- url     : https://prove2.me/submissions/844729bd-6b69-4e63-b28a-caf0272b6b2e

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IwasawaDecompositionAdelicSL2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Iwasawa
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.Iwasawa
theorem _root_.solution (b : F) : idem b ∈ Oh F := fun v => by
  by_cases h : IntAt b v
  · rw [idem_int h]; exact (v.adicCompletionIntegers F).one_mem
  · rw [idem_not h]; exact (v.adicCompletionIntegers F).zero_mem
end GlobalTheory.CompanionTheory.SW.Iwasawa
