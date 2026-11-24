-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetTop.algebraMap_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:45:10.084335+00:00
-- url     : https://prove2.me/submissions/e4b96d53-f758-489b-b649-5865f4b71f15

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetUnitIdealIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetTop_valued_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.CosetTop
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.Equi.CosetTop
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    algebraMap F (Fv F v) z ∈ v.adicCompletionIntegers F ↔ v.valuation F z ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
end GlobalTheory.CompanionTheory.Equi.CosetTop
