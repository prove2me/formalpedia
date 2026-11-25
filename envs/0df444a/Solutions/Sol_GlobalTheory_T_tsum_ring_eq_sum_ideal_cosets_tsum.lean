-- Prove2me | solution 1 for GlobalTheory.T.tsum_ring_eq_sum_ideal_cosets_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:41.409578+00:00
-- url     : https://prove2.me/submissions/21447256-a975-45b1-8980-06bc7d7368d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumRingEqSumIdealCosetsTsum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumRingEqSumIdealCosetsTsumStatement
import Theorems.Thm_GlobalTheory_cosets_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (M : Ideal R) [Fintype (R ⧸ M)] (h : R → ℂ), Summable h → ∑' α, h α = ∑ c : R ⧸ M, ∑' μ : M, h (Quotient.out c + μ) := by
  first | exact @GlobalTheory.cosets_main | exact GlobalTheory.cosets_main | (intros; apply GlobalTheory.cosets_main <;> assumption)
end _root_.GlobalTheory.T
