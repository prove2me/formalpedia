-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGL.prod_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:31:33.111809+00:00
-- url     : https://prove2.me/submissions/fbb9f7b3-9e94-4443-88da-c2de8c2b7cb6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGL
namespace GlobalTheory.CompanionTheory.FinGL
theorem _root_.solution (q : ℤ) (n : ℕ) :
    ∏ i ∈ Finset.range n, (q ^ n - q ^ i) =
      q ^ n.choose 2 * ∏ i ∈ Finset.Icc 1 n, (q ^ i - 1) := by
  have h1 : ∀ i ∈ Finset.range n, q ^ n - q ^ i = q ^ i * (q ^ (n - i) - 1) := by
    intro i hi
    have hin : i ≤ n := (Finset.mem_range.mp hi).le
    rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hin, mul_one]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id, Nat.choose_two_right]
  congr 1
  refine Finset.prod_nbij' (fun i => n - i) (fun j => n - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
    omega
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    show n - (n - i) = i
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    show n - (n - j) = j
    omega
  · intro i _
    rfl
end GlobalTheory.CompanionTheory.FinGL
