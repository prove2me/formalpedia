-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Iwasawa.Oh_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:24:17.007356+00:00
-- url     : https://prove2.me/submissions/a247f429-f011-4afb-bfae-802c66b6cf4d

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
theorem _root_.solution {x : A F} (hx : x ∈ Oh F) : -x ∈ Oh F := fun v =>
  (v.adicCompletionIntegers F).neg_mem _ (hx v)
end GlobalTheory.CompanionTheory.SW.Iwasawa
