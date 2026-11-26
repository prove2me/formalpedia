-- Prove2me | solution 1 for NisanRonen.Rounding.rounded_problem_exact_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:35:47.341721+00:00
-- url     : https://prove2.me/submissions/18f333de-d2d1-4266-9191-209842248d01

import Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_exact
import Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_polytime

open NisanRonen.Rounding

theorem solution {a b δ : ℝ} (ha : 0 < a) (_hab : a < b) (hδ : 0 < δ)
    (n : ℕ) [NeZero n] :
    ∃ f : List (Fin n → ℕ) → List (Fin n),
      Nonempty (Turing.TM2ComputableInPolyTime (encodeInstance (n := n))
        (id : List (Fin n) → List (Fin n)) f) ∧
      IsExactRoundedSolver f δ a b := by
  refine ⟨boundedLoadDP ⌈b / δ⌉.toNat, boundedLoadDP_polytime n _, ?_⟩
  exact boundedLoadDP_exact ha hδ n
