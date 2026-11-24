-- Prove2me | solution 1 for GlobalTheory.meanSq_card_primeFactors_outPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:20:02.968643+00:00
-- url     : https://prove2.me/submissions/e1314ab8-bb8a-401e-9d54-695e07828539

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqIocLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumDivSubLeTwoLogOfPartialSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MeanSqCardPrimeFactorsOutPart
import Theorems.Thm_GlobalTheory_meanSq_primeFactors_outPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2
namespace GlobalTheory
theorem _root_.solution (m₀ : ℕ) {n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n') :
    (outPart m₀ (n * n')).primeFactors.card ≤ 2 := by
  rw [meanSq_primeFactors_outPart]
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Nat.primeFactors_mul hn.ne_zero hn'.ne_zero]
  refine (Finset.card_union_le _ _).trans ?_
  rw [isPrimePow_iff_card_primeFactors_eq_one.1 hn, isPrimePow_iff_card_primeFactors_eq_one.1 hn']
end GlobalTheory
