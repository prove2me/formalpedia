-- Prove2me | solution 1 for N25.K2Rows.local_coboundary_lift_at_five
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:58.123078+00:00
-- url     : https://prove2.me/submissions/6f177591-6dca-414b-abe4-6f498f4ad2df

import Definitions.Def_N25_LocalKummerKernel
import Theorems.Thm_N25_chi71_frobenius_witness
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace

set_option autoImplicit false

noncomputable section

namespace N25

local instance fact_prime_seventyOne_K2Rows_lift_s6ee148 : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- A cocycle in the character line which becomes a coboundary in the middle
term at five was already a coboundary in the line. -/
theorem _root_.solution
    (hK2 : K2Rows) (c : G5 → ZMod 71) (b : ↥V)
    (hc : ∀ τ, hK2.i (c τ) = vAct (r5 τ) b - b) :
    ∃ a : ZMod 71, ∀ τ, c τ = (psi (r5 τ) : ZMod 71) * a - a := by
  have hqi (a : ZMod 71) : hK2.q (hK2.i a) = 0 := by
    change hK2.i a ∈ hK2.q.ker
    rw [hK2.exact_at_V]
    exact ⟨a, rfl⟩
  obtain ⟨φ, _, hφ⟩ := chi71_frobenius_witness
  have heq := congrArg hK2.q (hc φ)
  rw [hqi, map_sub, hK2.q_galois, hφ] at heq
  change 0 = (5 : ZMod 71) * hK2.q b - hK2.q b at heq
  have hqb : hK2.q b = 0 := by
    have hz : (5 - (1 : ZMod 71)) * hK2.q b = 0 := by
      linear_combination -heq
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have hb : b ∈ hK2.i.range := by
    rw [← hK2.exact_at_V]
    exact hqb
  obtain ⟨a, rfl⟩ := hb
  refine ⟨a, fun τ => hK2.i_injective ?_⟩
  rw [map_sub, hc τ, hK2.i_galois]

end N25
