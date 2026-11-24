-- Prove2me | solution 1 for GlobalTheory.T.iwasawa_decomposition_adelic_SL2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:17:08.439144+00:00
-- url     : https://prove2.me/submissions/074f03e8-b2ea-4635-805b-d41c52f0682b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IwasawaDecompositionAdelicSL2
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IwasawaDecompositionAdelicSL2Statement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_iwasawa_w_n


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], ∀ b : F, ∃ (y : A F) (a : (A F)ˣ) (k : SL(2, A F)), (∀ i j, k i j ∈ Oh F) ∧ wMat * nMat (algebraMap F (A F) b) = nMat y * mMat a * k ∧ (fun x => (a : A F) * x) '' Oh F = {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} := by
  first | exact @GlobalTheory.CompanionTheory.SW.Iwasawa.iwasawa_w_n | exact GlobalTheory.CompanionTheory.SW.Iwasawa.iwasawa_w_n | (intros; apply GlobalTheory.CompanionTheory.SW.Iwasawa.iwasawa_w_n <;> assumption)
end _root_.GlobalTheory.T
