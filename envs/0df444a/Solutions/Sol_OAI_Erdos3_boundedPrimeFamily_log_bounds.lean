-- Prove2me | solution 1 for OAI.Erdos3.boundedPrimeFamily_log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:22:27.093408+00:00
-- url     : https://prove2.me/submissions/fa8b600b-82bb-4734-b9ca-bb90286dbed4

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeDepthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boundedPrime_le (Q : ℕ) (p : BoundedPrime Q) : boundedPrime Q p ≤ Q :=
  ((mem_boundedPrimes Q p.val).mp p.property).2

theorem boundedPrimePower_le (Q : ℕ) (p : BoundedPrime Q) : boundedPrimePower Q p ≤ Q := by
  have hQ : 0 < Q := (boundedPrime_prime Q p).pos.trans_le (boundedPrime_le Q p)
  exact Nat.pow_log_le_self p.val hQ.ne'

theorem boundedPrime_card_le (Q : ℕ) : Fintype.card (BoundedPrime Q) ≤ Q := by
  have hsub : boundedPrimes Q ⊆ (Finset.range (Q + 1)).erase 0 := by
    intro p hp
    have h := (mem_boundedPrimes Q p).mp hp
    exact Finset.mem_erase.mpr ⟨h.1.ne_zero, Finset.mem_range.mpr (by omega)⟩
  calc
    _ = (boundedPrimes Q).card := Fintype.card_coe _
    _ ≤ ((Finset.range (Q + 1)).erase 0).card := Finset.card_le_card hsub
    _ = Q := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeFamilyCutoff
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem boundedPrimeFamily_log_bounds (Q : ℕ) {P : ℝ} (hQ : (Q : ℝ) ≤ Real.exp P) :
    (Fintype.card (BoundedPrime Q) : ℝ) ≤ Real.exp P ∧
      ∀ p : BoundedPrime Q, (boundedPrimePower Q p : ℝ) ≤ Real.exp P := by
  exact ⟨(Nat.cast_le.mpr (boundedPrime_card_le Q)).trans hQ,
    fun p => (Nat.cast_le.mpr (boundedPrimePower_le Q p)).trans hQ⟩

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.boundedPrimeFamily_log_bounds := @OAI.Erdos3.boundedPrimeFamily_log_bounds
