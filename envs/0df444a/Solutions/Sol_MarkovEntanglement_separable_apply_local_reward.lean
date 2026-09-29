-- Prove2me | solution 1 for MarkovEntanglement.separable_apply_local_reward
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T15:33:58.152688+00:00
-- url     : https://prove2.me/submissions/e3d41dd1-d704-4be3-bcbf-8a59eeafb3cf

import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

private theorem sum_prod_apply {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (S i)] (i : Fin N) (f : ∀ j, S j → ℝ)
    (hf : ∀ j, j ≠ i → ∑ s, f j s = 1) (g : S i → ℝ) :
    ∑ q : (∀ j, S j), (∏ j, f j (q j)) * g (q i) = ∑ t : S i, f i t * g t := by
  classical
  set f' : ∀ j, S j → ℝ := Function.update f i (fun t => f i t * g t) with hf'
  have hfi : f' i = fun t => f i t * g t := by rw [hf']; exact Function.update_self _ _ _
  have hfj : ∀ j, j ≠ i → f' j = f j := by
    intro j hj
    rw [hf']
    exact Function.update_of_ne hj _ _
  have hprod : ∀ q : (∀ j, S j), ∏ j, f' j (q j) = (∏ j, f j (q j)) * g (q i) := by
    intro q
    rw [Fintype.prod_eq_mul_prod_compl i (fun j => f' j (q j)),
      Fintype.prod_eq_mul_prod_compl i (fun j => f j (q j)), hfi]
    have h2 : ∀ j ∈ ({i}ᶜ : Finset (Fin N)), f' j (q j) = f j (q j) := by
      intro j hj
      simp only [Finset.mem_compl, Finset.mem_singleton] at hj
      rw [hfj j hj]
    rw [Finset.prod_congr rfl h2]
    ring
  calc ∑ q : (∀ j, S j), (∏ j, f j (q j)) * g (q i)
      = ∑ q : (∀ j, S j), ∏ j, f' j (q j) :=
        Finset.sum_congr rfl (fun q _ => (hprod q).symm)
    _ = ∏ j, ∑ s : S j, f' j s := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∑ t : S i, f i t * g t := by
        rw [Fintype.prod_eq_mul_prod_compl i (fun j => ∑ s : S j, f' j s)]
        have h3 : ∀ j ∈ ({i}ᶜ : Finset (Fin N)), (∑ s : S j, f' j s) = 1 := by
          intro j hj
          simp only [Finset.mem_compl, Finset.mem_singleton] at hj
          rw [hfj j hj]
          exact hf j hj
        rw [Finset.prod_congr rfl h3, Finset.prod_const_one, mul_one, hfi]

theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    {K : ℕ} (x : Fin K → ℝ) (Pj : Fin K → ∀ i, Matrix (S i) (S i) ℝ)
    (hPj : ∀ k i, IsTransitionMatrix (Pj k i)) (hx : ∑ k, x k = 1)
    (i : Fin N) (r : S i → ℝ) (p : Joint S) :
    ∑ q : Joint S, (∑ k, x k • tensorProdN (Pj k)) p q * r (q i)
      = ∑ k, x k * ∑ t : S i, Pj k i (p i) t * r t := by
  classical
  have hexp : ∀ q : Joint S, (∑ k, x k • tensorProdN (Pj k)) p q
      = ∑ k, x k * ∏ j, Pj k j (p j) (q j) := by
    intro q
    simp [tensorProdN, Matrix.sum_apply, Matrix.smul_apply]
  calc ∑ q : Joint S, (∑ k, x k • tensorProdN (Pj k)) p q * r (q i)
      = ∑ q : Joint S, ∑ k, x k * ((∏ j, Pj k j (p j) (q j)) * r (q i)) := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [hexp q, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k _ => by ring)
    _ = ∑ k, x k * ∑ q : Joint S, (∏ j, Pj k j (p j) (q j)) * r (q i) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun k _ => (Finset.mul_sum _ _ _).symm)
    _ = ∑ k, x k * ∑ t : S i, Pj k i (p i) t * r t := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [sum_prod_apply i (fun j => Pj k j (p j)) (fun j _ => (hPj k j).2 (p j)) r]
