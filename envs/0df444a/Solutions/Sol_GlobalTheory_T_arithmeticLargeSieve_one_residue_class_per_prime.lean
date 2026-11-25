-- Prove2me | solution 1 for GlobalTheory.T.arithmeticLargeSieve_one_residue_class_per_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:37.893128+00:00
-- url     : https://prove2.me/submissions/a20c73f1-4870-483e-b918-037f7b0e6c26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ArithmeticLargeSieveOneResidueClassPerPrime
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ArithmeticLargeSieveOneResidueClassPerPrimeStatement
import Theorems.Thm_GlobalTheory_arithmetic_large_sieve_one_class


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M N Q q : ℕ) (S : Finset ℕ), 1 ≤ Q → 1 ≤ q → S ⊆ Finset.Ioc M (M + N) → (∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q → ∃ c : ℕ, ∀ n ∈ S, ¬ n ≡ c [MOD p]) → (S.card : ℝ) * ((q.totient : ℝ) / q * Real.log Q) ≤ (Q : ℝ) ^ 2 + 2 * Real.pi * N := by
  first | exact @GlobalTheory.arithmetic_large_sieve_one_class | exact GlobalTheory.arithmetic_large_sieve_one_class | (intros; apply GlobalTheory.arithmetic_large_sieve_one_class <;> assumption)
end _root_.GlobalTheory.T
