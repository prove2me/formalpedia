-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Iwasawa.scale_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:22.436854+00:00
-- url     : https://prove2.me/submissions/01aef66b-8cf5-4991-9b2c-785d998fef3b

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
theorem _root_.solution (b : F) : scale b ∈ Oh F := fun v => by
  by_cases h : IntAt b v
  · rw [scale_int h]; exact (v.adicCompletionIntegers F).one_mem
  · rw [scale_not h]
    exact ((v.adicCompletionIntegers F).mem_or_inv_mem _).resolve_left h
end GlobalTheory.CompanionTheory.SW.Iwasawa
