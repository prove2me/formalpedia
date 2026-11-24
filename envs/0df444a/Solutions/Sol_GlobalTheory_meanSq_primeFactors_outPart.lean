-- Prove2me | solution 1 for GlobalTheory.meanSq_primeFactors_outPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:08:36.373787+00:00
-- url     : https://prove2.me/submissions/44c778c9-35f7-4e2b-88b4-7b47fe81b750

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
theorem _root_.solution (m₀ m : ℕ) :
    (outPart m₀ m).primeFactors = m.primeFactors.filter (fun p => ¬ p ∣ m₀ ∧ Odd (m.factorization p)) := by
  unfold outPart
  exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1
end GlobalTheory
