-- Prove2me | solution 1 for GlobalTheory.meanSq_abs_mean_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:20:01.663806+00:00
-- url     : https://prove2.me/submissions/4851b475-2ce7-4f60-9073-009963eba650

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqIocLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumDivSubLeTwoLogOfPartialSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MeanSqCardPrimeFactorsOutPart

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
theorem _root_.solution (PPs : Finset ℕ) (a : ℤ) :
    |(∑ q ∈ PPs, (jacobiSym a q : ℝ)) / PPs.card| ≤ 1 := by
  rw [abs_div, Nat.abs_cast]
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ q ∈ PPs, |(jacobiSym a q : ℝ)| ≤ 1 := by
    intro q _
    rcases jacobiSym.trichotomy a q with h | h | h <;> simp [h]
  simpa using Finset.sum_le_card_nsmul _ _ _ this
end GlobalTheory
