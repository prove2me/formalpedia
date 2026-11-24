-- Prove2me | solution 1 for GlobalTheory.cosets_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:22.215539+00:00
-- url     : https://prove2.me/submissions/3e612ac1-9a2f-43cd-b831-73237165df2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumRingEqSumIdealCosetsTsum
import Theorems.Thm_GlobalTheory_tsum_eq_sum_quotient_tsum_ideal

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] (M : Ideal R) [Fintype (R ⧸ M)] (h : R → ℂ), Summable h → ∑' α, h α = ∑ c : R ⧸ M, ∑' μ : M, h (Quotient.out c + μ) :=
  fun R _ M _ h hs => tsum_eq_sum_quotient_tsum_ideal R M h hs
end GlobalTheory
