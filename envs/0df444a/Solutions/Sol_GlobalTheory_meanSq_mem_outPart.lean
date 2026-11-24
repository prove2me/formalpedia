-- Prove2me | solution 1 for GlobalTheory.meanSq_mem_outPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:20:07.116874+00:00
-- url     : https://prove2.me/submissions/0e9f1b70-911a-4dad-b751-cd726b4cd374

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
theorem _root_.solution (m₀ : ℕ) {n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n')
    (hne : n.minFac ≠ n'.minFac) (hsq : ¬ IsSquare n) (hm : ¬ n.minFac ∣ m₀) :
    n.minFac ∈ (outPart m₀ (n * n')).primeFactors := by
  obtain ⟨p, i, hp, hi, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  obtain ⟨p', j, hp', hj, rfl⟩ := (isPrimePow_nat_iff _).1 hn'
  rw [hp.pow_minFac hi.ne'] at hne hm ⊢
  rw [hp'.pow_minFac hj.ne'] at hne
  rw [meanSq_primeFactors_outPart, Finset.mem_filter]
  refine ⟨Nat.mem_primeFactors.2 ⟨hp, Dvd.dvd.mul_right (dvd_pow_self p hi.ne') _,
    mul_ne_zero hn.ne_zero hn'.ne_zero⟩, hm, ?_⟩
  rw [Nat.factorization_mul hn.ne_zero hn'.ne_zero, hp.factorization_pow, hp'.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne, add_zero]
  rw [← Nat.not_even_iff_odd]
  exact fun h => hsq (h.isSquare_pow p)
end GlobalTheory
