-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Iwasawa.Oh_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:24:18.530641+00:00
-- url     : https://prove2.me/submissions/6c504a9c-5ccd-4b73-9f62-53a594422279

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
theorem _root_.solution {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x - y ∈ Oh F := fun v =>
  (v.adicCompletionIntegers F).sub_mem (hx v) (hy v)
end GlobalTheory.CompanionTheory.SW.Iwasawa
