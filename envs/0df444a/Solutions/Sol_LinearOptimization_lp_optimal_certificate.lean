-- Prove2me | solution 1 for LinearOptimization.lp_optimal_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T20:59:47.158577+00:00
-- url     : https://prove2.me/submissions/7ac70b37-eb12-44ee-b181-498d4291e986

import Theorems.Thm_LinearOptimization_lp_weak_duality

open Matrix

theorem solution {m n : ℕ} (P : LinearOptimization.GeneralFormLP m n)
    (x : Fin n → ℝ) (hx : x ∈ LinearOptimization.generalFeasibleSet P)
    (p : Fin m → ℝ)
    (hp : p ∈ LinearOptimization.generalFeasibleSet (LinearOptimization.dualLP P))
    (heq : p ⬝ᵥ P.b = P.c ⬝ᵥ x) :
    LinearOptimization.IsLpOptimal P.c (LinearOptimization.generalFeasibleSet P) x ∧
    LinearOptimization.IsLpDualOptimal P.b
      (LinearOptimization.generalFeasibleSet (LinearOptimization.dualLP P)) p := by
  constructor
  · refine ⟨hx, ?_⟩
    intro y hy
    rw [← heq]
    exact LinearOptimization.lp_weak_duality P y hy p hp
  · refine ⟨hp, ?_⟩
    intro q hq
    rw [heq]
    exact LinearOptimization.lp_weak_duality P x hx q hq
