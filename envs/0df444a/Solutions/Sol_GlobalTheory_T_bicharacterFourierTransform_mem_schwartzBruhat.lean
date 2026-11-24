-- Prove2me | solution 1 for GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:49:52.446348+00:00
-- url     : https://prove2.me/submissions/92c98ffe-f240-417e-ac4b-0cd64eb9119f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformMemSchwartzBruhat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformMemSchwartzBruhatStatement
import Theorems.Thm_GlobalTheory_KSp_FourMem_four_mem_SB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ φ ∈ SB X, four μ e φ ∈ SB X := by
  first | exact @GlobalTheory.KSp.FourMem.four_mem_SB | exact GlobalTheory.KSp.FourMem.four_mem_SB | (intros; apply GlobalTheory.KSp.FourMem.four_mem_SB <;> assumption)
end _root_.GlobalTheory.T
