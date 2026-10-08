-- Prove2me | solution 1 for IgnallSchrage.MeanCompletion.example_p408
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:53:13.348527+00:00
-- url     : https://prove2.me/submissions/ab194675-5cd4-40bd-8c1a-470fd2bf8be4

import Mathlib
import Definitions.Def_IgnallSchrage_MeanCompletion_Node
open IgnallSchrage.MeanCompletion
set_option autoImplicit false
set_option maxHeartbeats 400000
private lemma positional {n : ℕ} (a b : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    totalCompletion a b σ = ∑ i : Fin n, JohnsonFlowShop.TwoStage.asapC2 a b σ (i.val+1) := by
  unfold totalCompletion completionTime
  rw [← Equiv.sum_comp σ]
  simp
private lemma iic_filter {n : ℕ} (i : Fin n) :
    Finset.Iic i = Finset.univ.filter (fun j => j ≤ i) := by ext; simp
theorem solution :
    (totalCompletion (n := 2) ![2, 10] ![11, 3] 1 = 29 ∧
      totalCompletion (n := 2) ![2, 10] ![11, 3] (Equiv.swap 0 1) = 37 ∧
      ∀ σ : Equiv.Perm (Fin 2),
        totalCompletion (n := 2) ![2, 10] ![11, 3] 1 ≤ totalCompletion ![2, 10] ![11, 3] σ) ∧
    (totalCompletion (n := 3) ![2, 10, 1] ![11, 3, 8] (Equiv.swap 0 2) = 48 ∧
      ∀ σ : Equiv.Perm (Fin 3),
        totalCompletion (n := 3) ![2, 10, 1] ![11, 3, 8] (Equiv.swap 0 2) ≤
          totalCompletion ![2, 10, 1] ![11, 3, 8] σ) := by
  classical
  have e2 : totalCompletion (n := 2) ![2,10] ![11,3] 1 = 29 := by
    rw [positional]
    norm_num [JohnsonFlowShop.TwoStage.asapC2, iic_filter, Finset.sum_filter,
      Fin.sum_univ_succ]
  have e2' : totalCompletion (n := 2) ![2,10] ![11,3] (Equiv.swap 0 1) = 37 := by
    rw [positional]
    norm_num [JohnsonFlowShop.TwoStage.asapC2, iic_filter, Finset.sum_filter,
      Fin.sum_univ_succ, Equiv.swap_apply_def, Matrix.cons_val_two, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      (show (2 : Fin 3) ≠ 0 by decide), (show (2 : Fin 3) ≠ 1 by decide), (show (1 : Fin 3) ≠ 2 by decide),
      (show ¬ (2 : Fin 3) ≤ 1 by decide), (show (1 : Fin 3) ≤ 2 by decide)]
  have e3 : totalCompletion (n := 3) ![2,10,1] ![11,3,8] (Equiv.swap 0 2) = 48 := by
    rw [positional]
    norm_num [JohnsonFlowShop.TwoStage.asapC2, iic_filter, Finset.sum_filter,
      Fin.sum_univ_succ, Equiv.swap_apply_def, Matrix.cons_val_two, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      (show (2 : Fin 3) ≠ 0 by decide), (show (2 : Fin 3) ≠ 1 by decide), (show (1 : Fin 3) ≠ 2 by decide),
      (show ¬ (2 : Fin 3) ≤ 1 by decide), (show (1 : Fin 3) ≤ 2 by decide)]
  refine ⟨⟨e2,e2',?_⟩,e3,?_⟩
  · intro σ
    rw [e2, positional]
    have h01 : σ 0 ≠ σ 1 := fun he => (by decide : (0 : Fin 2) ≠ 1) (σ.injective he)
    generalize h0 : σ 0 = j0 at h01
    generalize h1 : σ 1 = j1 at h01
    fin_cases j0 <;> fin_cases j1 <;> simp at h01
    all_goals norm_num [JohnsonFlowShop.TwoStage.asapC2, iic_filter, Finset.sum_filter,
      Fin.sum_univ_succ, h0, h1, Matrix.cons_val_two, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      (show (2 : Fin 3) ≠ 0 by decide), (show (2 : Fin 3) ≠ 1 by decide), (show (1 : Fin 3) ≠ 2 by decide),
      (show ¬ (2 : Fin 3) ≤ 1 by decide), (show (1 : Fin 3) ≤ 2 by decide)]
  · intro σ
    rw [e3, positional]
    have h01 : σ 0 ≠ σ 1 := fun he => (by decide : (0 : Fin 3) ≠ 1) (σ.injective he)
    have h02 : σ 0 ≠ σ 2 := fun he => (by decide : (0 : Fin 3) ≠ 2) (σ.injective he)
    have h12 : σ 1 ≠ σ 2 := fun he => (by decide : (1 : Fin 3) ≠ 2) (σ.injective he)
    generalize h0 : σ 0 = j0 at h01 h02
    generalize h1 : σ 1 = j1 at h01 h12
    generalize h2 : σ 2 = j2 at h02 h12
    fin_cases j0 <;> fin_cases j1 <;> fin_cases j2 <;> simp at h01 h02 h12
    all_goals norm_num [JohnsonFlowShop.TwoStage.asapC2, iic_filter, Finset.sum_filter,
      Fin.sum_univ_succ, h0, h1, h2, Matrix.cons_val_two, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      (show (2 : Fin 3) ≠ 0 by decide), (show (2 : Fin 3) ≠ 1 by decide), (show (1 : Fin 3) ≠ 2 by decide),
      (show ¬ (2 : Fin 3) ≤ 1 by decide), (show (1 : Fin 3) ≤ 2 by decide)]
#print axioms solution
