-- Prove2me | solution 1 for GlobalTheory.UnipotentInvariant.biInvariant_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:48.917407+00:00
-- url     : https://prove2.me/submissions/93dcdedd-7e50-4620-8d65-405eb4cf4d57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
import Theorems.Thm_GlobalTheory_UnipotentInvariant_setBlock_apply
import Theorems.Thm_GlobalTheory_UnipotentInvariant_setBlock_of_not
import Theorems.Thm_P2M_GlobalTheory_UnipotentInvariant_eval_bind___d799cbbaf6da

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}
variable {σ : Type*} [DecidableEq σ]
namespace GlobalTheory.UnipotentInvariant
theorem _root_.solution {z : Fin p × Fin p → σ} (hz : Function.Injective z)
    (P : MvPolynomial σ K)
    (hr : ∀ a b : Fin p, a < b → ∀ t : K,
      bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P)
    (hc : ∀ k l : Fin p, k < l → ∀ t : K,
      bind₁ (fun s => X s + ∑ a, if s = z (a, l) then C t * X (z (a, k)) else 0) P = P)
    (x : σ → K) : BiInvariant fun M => eval (setBlock z x M) P := by
  constructor
  · intro a b hab t M
    beta_reduce
    conv_rhs => rw [← hr a b hab t, eval_bind₁']
    congr 2
    funext s
    by_cases hs : ∃ w, z w = s
    · obtain ⟨⟨u, v⟩, rfl⟩ := hs
      simp only [setBlock_apply hz, map_add, eval_X, map_sum, hz.eq_iff, Prod.mk.injEq,
        apply_ite (eval (setBlock z x M)), map_mul, eval_C, map_zero, rowAdd, of_apply]
      by_cases hu : u = b <;> simp [hu]
    · have : ∀ w, s ≠ z w := fun w h => hs ⟨w, h.symm⟩
      simp [setBlock_of_not _ _ hs, this]
  · intro a b hab t M
    beta_reduce
    conv_rhs => rw [← hc a b hab t, eval_bind₁']
    congr 2
    funext s
    by_cases hs : ∃ w, z w = s
    · obtain ⟨⟨u, v⟩, rfl⟩ := hs
      simp only [setBlock_apply hz, map_add, eval_X, map_sum, hz.eq_iff, Prod.mk.injEq,
        apply_ite (eval (setBlock z x Mᵀ)), map_mul, eval_C, map_zero, rowAdd, of_apply,
        transpose_apply]
      by_cases hu : v = b <;> simp [hu]
    · have : ∀ w, s ≠ z w := fun w h => hs ⟨w, h.symm⟩
      simp [setBlock_of_not _ _ hs, this]
end GlobalTheory.UnipotentInvariant
