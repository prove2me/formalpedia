-- Prove2me | solution 1 for GlobalTheory.eval_rowOps_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:38:09.2904+00:00
-- url     : https://prove2.me/submissions/43b4a45c-c12f-4672-8b26-58c6b5f924fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ColumnDegreeLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K σ : Type*} [Field K] [DecidableEq σ] {p n : ℕ} (z : Fin p × Fin n → σ)
    (hz : Function.Injective z) (P : MvPolynomial σ K)
    (hinv : ∀ a b : Fin p, a < b → ∀ t : K,
      bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P)
    (i : ℕ) (c : Fin p × Fin p → K) (x : σ → K) (T : Finset (Fin p × Fin p))
    (hT : ∀ q ∈ T, (q.1 : ℕ) < i ∧ i ≤ (q.2 : ℕ)) :
    eval (fun s => x s + ∑ q ∈ T, ∑ k, if s = z (q.2, k) then c q * x (z (q.1, k)) else 0) P
      = eval x P := by
  have hb : ∀ (y : σ → K) (f : σ → MvPolynomial σ K) (Q : MvPolynomial σ K),
      eval y (bind₁ f Q) = eval (fun s => eval y (f s)) Q :=
    fun y f Q => eval₂Hom_bind₁ _ _ _ _
  revert hT
  refine Finset.induction_on T ?_ ?_
  · intro _
    simp
  · intro q T hq ih hT
    have hq' := hT q (Finset.mem_insert_self q T)
    have hab : q.1 < q.2 := Fin.lt_def.2 (lt_of_lt_of_le hq'.1 hq'.2)
    set y : σ → K := fun s => x s + ∑ q' ∈ T, ∑ k, if s = z (q'.2, k) then c q' * x (z (q'.1, k)) else 0
      with hy_def
    have hy : ∀ k, y (z (q.1, k)) = x (z (q.1, k)) := by
      intro k
      rw [hy_def]
      simp only [add_eq_left]
      refine Finset.sum_eq_zero fun q' hq'T => Finset.sum_eq_zero fun k' _ => ?_
      rw [if_neg]
      intro h
      have h2 := congrArg Prod.fst (hz h)
      have h3 := hT q' (Finset.mem_insert_of_mem hq'T)
      have : (q.1 : ℕ) < q'.2 := lt_of_lt_of_le hq'.1 h3.2
      simp only at h2
      rw [h2] at this
      exact lt_irrefl _ this
    have hfun : (fun s => x s + ∑ q' ∈ insert q T, ∑ k,
        if s = z (q'.2, k) then c q' * x (z (q'.1, k)) else 0) =
        fun s => eval y (X s + ∑ k, if s = z (q.2, k) then C (c q) * X (z (q.1, k)) else 0) := by
      funext s
      have he : ∀ k, eval y (if s = z (q.2, k) then C (c q) * X (z (q.1, k)) else 0) =
          if s = z (q.2, k) then c q * x (z (q.1, k)) else 0 := by
        intro k
        split_ifs
        · simp [hy]
        · simp
      rw [map_add, eval_X, map_sum, Finset.sum_congr rfl fun k _ => he k, Finset.sum_insert hq, hy_def]
      ring
    rw [hfun, ← hb, hinv q.1 q.2 hab (c q), ih fun q' h => hT q' (Finset.mem_insert_of_mem h)]
end GlobalTheory
