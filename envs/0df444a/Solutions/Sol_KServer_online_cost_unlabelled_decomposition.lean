-- Prove2me | solution 1 for KServer.online_cost_unlabelled_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T22:14:45.964532+00:00
-- url     : https://prove2.me/submissions/8ebff7ee-09ff-476c-a9db-b5eeeb158483

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFn_nil

open KServer

private theorem wfU_nil_self {k : ℕ} (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) : workFnU C₀ [] C₀ = 0 := by
  refine le_antisymm ?_ ?_
  · have h := ciInf_le (f := fun π : Equiv.Perm (Fin k) => workFn C₀ [] (C₀ ∘ π))
      (Finite.bddBelow_range _) (1 : Equiv.Perm (Fin k))
    have h0 : workFn C₀ [] (C₀ ∘ (1 : Equiv.Perm (Fin k))) = 0 := by
      have := workFn_nil k hk M C₀ (C₀ ∘ (1 : Equiv.Perm (Fin k)))
      rw [this]
      unfold moveCost
      simp
    rw [h0] at h
    simpa [workFnU] using h
  · refine le_ciInf fun π => ?_
    rw [workFn_nil k hk M C₀ (C₀ ∘ π)]
    exact Finset.sum_nonneg fun i _ => dist_nonneg

/-- **The unlabelled decomposition of an online algorithm's cost.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (A : OnlineAlgorithm k M) (σ : List M) :
    A.cost σ + workFnU (A.conf []) σ (A.conf σ)
      = (∑ t ∈ Finset.range σ.length,
          (moveCost (A.conf (σ.take t)) (A.conf (σ.take (t + 1)))
            - (workFnU (A.conf []) (σ.take (t + 1)) (A.conf (σ.take t))
               - workFnU (A.conf []) (σ.take (t + 1)) (A.conf (σ.take (t + 1))))))
        + ∑ t ∈ Finset.range σ.length,
          (workFnU (A.conf []) (σ.take (t + 1)) (A.conf (σ.take t))
            - workFnU (A.conf []) (σ.take t) (A.conf (σ.take t))) := by
  classical
  set C₀ : Config k M := A.conf [] with hC₀
  set S : ℕ → Config k M := fun t => A.conf (σ.take t) with hSdef
  set f : ℕ → ℝ := fun t => workFnU C₀ (σ.take t) (S t) with hfdef
  have hcomb : ∀ t ∈ Finset.range σ.length,
      (moveCost (S t) (S (t + 1))
          - (workFnU C₀ (σ.take (t + 1)) (S t) - f (t + 1)))
        + (workFnU C₀ (σ.take (t + 1)) (S t) - f t)
      = moveCost (S t) (S (t + 1)) + (f (t + 1) - f t) := by
    intro t _
    ring
  have hsum : (∑ t ∈ Finset.range σ.length,
        (moveCost (S t) (S (t + 1))
          - (workFnU C₀ (σ.take (t + 1)) (S t) - f (t + 1))))
      + ∑ t ∈ Finset.range σ.length,
        (workFnU C₀ (σ.take (t + 1)) (S t) - f t)
      = ∑ t ∈ Finset.range σ.length, (moveCost (S t) (S (t + 1)) + (f (t + 1) - f t)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hcomb
  have hsplit : (∑ t ∈ Finset.range σ.length, (moveCost (S t) (S (t + 1)) + (f (t + 1) - f t)))
      = (∑ t ∈ Finset.range σ.length, moveCost (S t) (S (t + 1)))
        + ∑ t ∈ Finset.range σ.length, (f (t + 1) - f t) :=
    Finset.sum_add_distrib
  have htel : (∑ t ∈ Finset.range σ.length, (f (t + 1) - f t)) = f σ.length - f 0 :=
    Finset.sum_range_sub f σ.length
  have hf0 : f 0 = 0 := by
    show workFnU C₀ (σ.take 0) (A.conf (σ.take 0)) = 0
    rw [List.take_zero]
    exact wfU_nil_self hk M C₀
  have hfn : f σ.length = workFnU C₀ σ (A.conf σ) := by
    show workFnU C₀ (σ.take σ.length) (A.conf (σ.take σ.length)) = workFnU C₀ σ (A.conf σ)
    rw [List.take_length]
  have hcost : A.cost σ = ∑ t ∈ Finset.range σ.length, moveCost (S t) (S (t + 1)) := rfl
  rw [hsum, hsplit, htel, hf0, hfn, ← hcost]
  ring
