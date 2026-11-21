-- Prove2me | solution 1 for MasulloGRH.strongDual_quasinuclear_domination
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:14:59.898623+00:00
-- url     : https://prove2.me/submissions/683490e7-1679-4dc5-b452-21cbbd900b01

import Theorems.Thm_MasulloGRH_strongDual_seminorm_le_polar
import Theorems.Thm_MasulloGRH_nuclearFrechet_bounded_nuclear_domination
import Theorems.Thm_MasulloGRH_strongDual_evaluation_seminorm

set_option autoImplicit false

open MasulloGRH in
theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E)
    (p : Seminorm ℂ (StrongDual ℂ E)) (hp : Continuous p) :
    ∃ (q : Seminorm ℂ (StrongDual ℂ E)) (f : ℕ → StrongDual ℂ (StrongDual ℂ E)) (c : ℕ → ℝ),
      Continuous q ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ q x) ∧
      ∀ x, p x ≤ ∑' n, c n * ‖f n x‖ := by
  obtain ⟨B, C, hB, hC, hpB⟩ := strongDual_seminorm_le_polar E hN.1 p hp
  obtain ⟨y, c, hy, hc0, hcs, hdom⟩ := nuclearFrechet_bounded_nuclear_domination E hE hN B hB
  obtain ⟨q, φ, hq, hφ, hqy⟩ := strongDual_evaluation_seminorm E hN.1 y hy
  refine ⟨q, φ, fun n => C * c n, hq, fun n => mul_nonneg hC (hc0 n), hcs.mul_left C, ?_, ?_⟩
  · intro n x; rw [hφ]; exact hqy n x
  · intro f
    have hS : 0 ≤ ∑' n, c n * ‖f (y n)‖ :=
      tsum_nonneg fun n => mul_nonneg (hc0 n) (norm_nonneg _)
    have := hpB f _ hS (hdom f)
    calc p f ≤ C * ∑' n, c n * ‖f (y n)‖ := this
      _ = ∑' n, C * c n * ‖φ n f‖ := by
        rw [← tsum_mul_left]; congr 1; ext n; rw [hφ, mul_assoc]
