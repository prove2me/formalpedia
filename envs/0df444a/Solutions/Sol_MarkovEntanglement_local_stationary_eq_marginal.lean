-- Prove2me | solution 1 for MarkovEntanglement.local_stationary_eq_marginal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-07T15:31:58.196061+00:00
-- url     : https://prove2.me/submissions/f0eaec68-6e12-493d-a68f-4931f50d1e91

import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

/-!
Chen and Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Lemma 5, pp. 38-39:
the local stationary distribution of each agent is exactly the marginal of the global
occupancy measure.

The proof is the chain of summation interchanges in the source, verifying the definition
of a stationary distribution directly.  Writing `m = marginalDist i μ`, for a fixed target
local state-action pair `t`:

* by `IsLocalTransitionN`, each summand `m s * Pi s t` equals
  `∑ p, (if p i = s then μ p else 0) * marginalN i P p t`;
* summing over `s` collapses the indicator (for each `p` exactly one `s`, namely `s = p i`,
  contributes), leaving `∑ p, μ p * marginalN i P p t`;
* expanding `marginalN` and exchanging the two sums turns this into
  `∑ q, if q i = t then (∑ p, μ p * P p q) else 0`;
* the inner sum is `μ q` by stationarity of `μ`, and what remains is `marginalDist i μ t`.

Neither `hP` nor `hμ` is needed: the identity is pure bookkeeping on top of `hstat`.
-/

theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (μ : Joint S → ℝ) (hμ : IsPositiveDist μ) (hstat : IsStationary P μ)
    (i : Fin N) (Pi : Matrix (S i) (S i) ℝ)
    (hPi : IsLocalTransitionN i P μ Pi) :
    IsStationary Pi (marginalDist i μ) := by
  classical
  intro t
  calc ∑ s : S i, marginalDist i μ s * Pi s t
      = ∑ s : S i, ∑ p : Joint S, (if p i = s then μ p else 0) * marginalN i P p t :=
        Finset.sum_congr rfl fun s _ => hPi s t
    _ = ∑ p : Joint S, ∑ s : S i, (if p i = s then μ p else 0) * marginalN i P p t :=
        Finset.sum_comm
    _ = ∑ p : Joint S, μ p * marginalN i P p t := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_mul]
        simp
    _ = marginalDist i μ t := by
        unfold marginalN marginalDist
        simp_rw [Finset.mul_sum, mul_ite, mul_zero]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        by_cases h : q i = t
        · simp only [if_pos h]
          exact hstat q
        · simp [h]
