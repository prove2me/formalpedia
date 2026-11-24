-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Iwasawa.Oh_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:24:16.214257+00:00
-- url     : https://prove2.me/submissions/07a19d3f-6537-4530-a260-94818726f52c

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
theorem _root_.solution {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x * y ∈ Oh F := fun v =>
  (v.adicCompletionIntegers F).mul_mem _ _ (hx v) (hy v)
end GlobalTheory.CompanionTheory.SW.Iwasawa
