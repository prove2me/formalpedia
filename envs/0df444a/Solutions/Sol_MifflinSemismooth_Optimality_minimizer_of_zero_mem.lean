-- Prove2me | solution 1 for MifflinSemismooth.Optimality.minimizer_of_zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:29:40.880298+00:00
-- url     : https://prove2.me/submissions/33832767-7808-4c5d-96ae-778fd0867715

import Mathlib
import Definitions.Def_MifflinSemismooth_Optimality_Setting

set_option autoImplicit false

theorem solution {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (xbar : EuclideanSpace ℝ (Fin n)) (hF : MifflinSemismooth.Extremal.SemiconvexAt Set.univ F xbar)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ MifflinSemismooth.Extremal.genGrad F xbar) :
    ∀ x, F xbar ≤ F x := by
  intro x
  obtain ⟨_, hq, hs⟩ := hF
  have hnn : 0 ≤ ClarkeGradients.Shared.genDirDeriv F xbar (x - xbar) := by
    have := h0 (x - xbar)
    simpa using this
  have := hs (x - xbar) _ (Set.mem_univ _) (hq (x - xbar)) hnn
  simpa using this
