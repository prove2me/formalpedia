-- Prove2me | solution 1 for GlobalTheory.MultinomialCount.card_mul_prod_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:37:42.325845+00:00
-- url     : https://prove2.me/submissions/62eda5e4-a5b0-4167-afa5-2b54dc406e16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardMultisetWordsMulFactorial
import Theorems.Thm_GlobalTheory_MultinomialCount_cons_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
open GlobalTheory GlobalTheory.MultinomialCount
namespace GlobalTheory.MultinomialCount
theorem _root_.solution : ∀ {I : Type} [Fintype I] (k : ℕ) (ν : I → ℕ), ∑ i, ν i = k →
    (Finset.univ.filter (fun s : Fin k → I => ∀ i, (List.ofFn s).count i = ν i)).card *
      ∏ i, (ν i).factorial = k.factorial := by
  intro I _ k
  induction k with
  | zero =>
    intro ν hν
    have h0 : ∀ i, ν i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hν) i (Finset.mem_univ _)
    have : (Finset.univ.filter (fun s : Fin 0 → I => ∀ i, (List.ofFn s).count i = ν i)) = Finset.univ := by
      ext s; simp [h0]
    rw [this]; simp [h0]
  | succ k ih =>
    intro ν hν
    rw [Finset.card_filter, ← (Fin.consEquiv (fun _ : Fin (k+1) => I)).sum_comp, Fintype.sum_prod_type]
    have key : ∀ a : I, (∑ t : Fin k → I, if (∀ i, (List.ofFn (Fin.consEquiv (fun _ : Fin (k+1) => I) (a, t))).count i = ν i) then 1 else 0) *
        ∏ i, (ν i).factorial = ν a * k.factorial := by
      intro a
      have hc : ∀ t : Fin k → I, (∀ i, (List.ofFn (Fin.consEquiv (fun _ : Fin (k+1) => I) (a, t))).count i = ν i) ↔
          (1 ≤ ν a ∧ ∀ i, (List.ofFn t).count i = Function.update ν a (ν a - 1) i) := fun t => cons_iff ν a t
      simp_rw [hc]
      by_cases ha : 1 ≤ ν a
      · simp only [ha, true_and]
        rw [← Finset.card_filter]
        set μ := Function.update ν a (ν a - 1) with hμ
        have hs1 : ∑ i, μ i = (ν a - 1) + ∑ i ∈ Finset.univ \ {a}, ν i := by
          rw [hμ, Finset.sum_update_of_mem (Finset.mem_univ a)]
        have hs2 : ∑ i, ν i = ν a + ∑ i ∈ Finset.univ \ {a}, ν i :=
          Fintype.sum_eq_add_sum_compl a _
        have hμs : ∑ i, μ i = k := by omega
        have h1 : ∏ i, (μ i).factorial = (ν a - 1).factorial * ∏ i ∈ Finset.univ \ {a}, (ν i).factorial := by
          rw [Fintype.prod_eq_mul_prod_compl a]
          congr 1
          · simp [hμ]
          · apply Finset.prod_congr rfl
            intro i hi
            simp only [Finset.mem_compl, Finset.mem_singleton] at hi
            simp [hμ, Function.update_apply, hi]
        have h2 : ∏ i, (ν i).factorial = (ν a).factorial * ∏ i ∈ Finset.univ \ {a}, (ν i).factorial :=
          Fintype.prod_eq_mul_prod_compl a _
        have h3 : (ν a).factorial = ν a * (ν a - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
        have hi := ih μ hμs
        rw [h1] at hi
        rw [h2, h3, ← hi]
        ring
      · have : ν a = 0 := by omega
        simp [ha, this]
    rw [Finset.sum_mul]
    simp_rw [key]
    rw [← Finset.sum_mul, hν, Nat.factorial_succ]
end GlobalTheory.MultinomialCount
