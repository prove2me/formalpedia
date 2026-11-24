-- Prove2me | solution 1 for GlobalTheory.UnipotentInvariant.eval_setBlock_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:49.904813+00:00
-- url     : https://prove2.me/submissions/acf42480-3ad9-46c7-a61e-c202ee8b1f2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
import Theorems.Thm_GlobalTheory_UnipotentInvariant_setBlock_apply
import Theorems.Thm_GlobalTheory_UnipotentInvariant_setBlock_of_not

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
    (P : MvPolynomial σ K) (l : Fin p → ℕ)
    (hrow : ∀ a, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = l a) (x : σ → K) (d : Fin p → K) :
    eval (setBlock z x (diagonal d)) P = eval (setBlock z x 1) P * ∏ a, d a ^ l a := by
  let w : σ → K := setBlock z 1 (Matrix.of fun a _ => d a)
  have hw : ∀ s, setBlock z x (diagonal d) s = setBlock z x 1 s * w s := by
    intro s
    by_cases hs : ∃ w, z w = s
    · obtain ⟨⟨u, v⟩, rfl⟩ := hs
      simp only [w, setBlock_apply hz, diagonal_apply, one_apply, of_apply]
      split_ifs <;> simp
    · simp [w, setBlock_of_not _ _ hs]
  rw [eval_eq, eval_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [hw, mul_pow, Finset.prod_mul_distrib, mul_assoc]
  congr 2
  have h1 : ∏ s ∈ m.support, w s ^ m s = ∏ s ∈ Finset.univ.image z, w s ^ m s := by
    refine Finset.prod_congr_of_eq_on_inter ?_ ?_ fun _ _ _ => rfl
    · intro s _ hs
      have hs' : ¬ ∃ w, z w = s := by simpa using hs
      simp [w, setBlock_of_not _ _ hs']
    · intro s _ hs
      rw [Finsupp.notMem_support_iff.mp hs, pow_zero]
  rw [h1, Finset.prod_image fun _ _ _ _ h => hz h, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← hrow a m hm, ← Finset.prod_pow_eq_pow_sum]
  simp [w, setBlock_apply hz]
end GlobalTheory.UnipotentInvariant
