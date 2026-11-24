-- Prove2me | solution 1 for GlobalTheory.capelli_casimir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:24:41.680766+00:00
-- url     : https://prove2.me/submissions/acf946c8-e3da-465f-be73-f0513f373cdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
import Theorems.Thm_GlobalTheory_Capelli_pderiv_swap
import Theorems.Thm_P2M_GlobalTheory_Capelli_pderiv_X_mul__2a5262d9a5e3
import Theorems.Thm_GlobalTheory_Capelli_polar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Capelli.polar_apply

set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open Capelli
namespace GlobalTheory
theorem _root_.solution {K σ : Type*} [CommRing K] [DecidableEq σ] {p n : ℕ} (z : Fin p × Fin n → σ) (hz : Function.Injective z) (P : MvPolynomial σ K) :
    (∑ k, ∑ l, ∑ a, X (z (a, k)) * pderiv (z (a, l)) (∑ b, X (z (b, l)) * pderiv (z (b, k)) P)) =
    (∑ a, ∑ b, ∑ k, X (z (a, k)) * pderiv (z (b, k)) (∑ l, X (z (b, l)) * pderiv (z (a, l)) P)) +
      ((n : K) - (p : K)) • ∑ w : Fin p × Fin n, X (z w) * pderiv (z w) P := by
  set E : MvPolynomial σ K := ∑ w : Fin p × Fin n, X (z w) * pderiv (z w) P with hE
  set S : MvPolynomial σ K := ∑ a, ∑ b, ∑ k, ∑ l, X (z (a, k)) * (X (z (b, l)) *
    pderiv (z (a, l)) (pderiv (z (b, k)) P)) with hS
  have h₁ : (∑ k, ∑ l, ∑ a, X (z (a, k)) * pderiv (z (a, l))
      (∑ b, X (z (b, l)) * pderiv (z (b, k)) P)) = S + (n : K) • E := by
    simp only [map_sum, pderiv_X_mul', hz.eq_iff, Prod.mk.injEq, and_true,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_add,
      Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · calc _ = ∑ k, ∑ a, ∑ b, ∑ l, X (z (a, k)) * (X (z (b, l)) *
            pderiv (z (a, l)) (pderiv (z (b, k)) P)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = _ := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    · rw [hE, Fintype.sum_prod_type_right, Finset.smul_sum]
      simp [Nat.cast_smul_eq_nsmul]
  have h₂ : (∑ a, ∑ b, ∑ k, X (z (a, k)) * pderiv (z (b, k))
      (∑ l, X (z (b, l)) * pderiv (z (a, l)) P)) = S + (p : K) • E := by
    simp only [map_sum, pderiv_X_mul', hz.eq_iff, Prod.mk.injEq, true_and,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_add,
      Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [hS]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [pderiv_swap]
    · rw [hE, Fintype.sum_prod_type, Finset.smul_sum]
      simp [Nat.cast_smul_eq_nsmul]
  rw [h₁, h₂, sub_smul]
  abel
end GlobalTheory
