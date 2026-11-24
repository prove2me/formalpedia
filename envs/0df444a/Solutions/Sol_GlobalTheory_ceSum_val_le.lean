-- Prove2me | solution 1 for GlobalTheory.ceSum_val_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:07.458811+00:00
-- url     : https://prove2.me/submissions/348f511b-2fdd-49fb-90be-f6f5eb04d0ca

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CmValuesExponentLogSumLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) (X : ℕ) :
    ∑ l ∈ S, (padicValNat l X : ℝ) * Real.log l ≤ Real.log X := by
  have h1 : ∑ l ∈ S, (padicValNat l X : ℝ) * Real.log l
      = ∑ l ∈ S, (X.factorization l : ℝ) * Real.log l := by
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Nat.factorization_def X (hS l hl)]
  rw [h1, Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have hsub : S ⊆ S ∪ X.factorization.support := Finset.subset_union_left
  calc ∑ l ∈ S, (X.factorization l : ℝ) * Real.log l
      ≤ ∑ l ∈ S ∪ X.factorization.support, (X.factorization l : ℝ) * Real.log l := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun l hl _ => ?_
        rcases Finset.mem_union.1 hl with h | h
        · exact mul_nonneg (Nat.cast_nonneg _)
            (Real.log_nonneg (by exact_mod_cast (hS l h).one_lt.le))
        · have hp : l.Prime := Nat.prime_of_mem_primeFactors (by simpa using h)
          exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
    _ = ∑ l ∈ X.factorization.support, (X.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_subset Finset.subset_union_right fun l _ hl => ?_).symm
        rw [Finsupp.notMem_support_iff.1 hl]
        simp
end GlobalTheory
