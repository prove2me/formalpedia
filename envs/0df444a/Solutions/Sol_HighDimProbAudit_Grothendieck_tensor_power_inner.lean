-- Prove2me | solution 1 for HighDimProbAudit.Grothendieck.tensor_power_inner
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:06:18.198066+00:00
-- url     : https://prove2.me/submissions/57cdfe7d-fb85-4cec-bf34-7b62c5993182

import Mathlib
import Definitions.Def_HighDimProbAudit_Grothendieck_TensorPowers

set_option autoImplicit false

open HighDimProbAudit.Grothendieck
open scoped BigOperators

theorem solution (n k : ℕ) (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (tensorPower k u) (tensorPower k v) = (inner ℝ u v) ^ k := by
  simp only [tensorPower, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  have h1 : ∑ t : Fin k → Fin n, (∏ r : Fin k, v (t r)) * (∏ r : Fin k, u (t r)) =
      ∑ t : Fin k → Fin n, ∏ r : Fin k, (v (t r) * u (t r)) := by
    refine Finset.sum_congr rfl fun t _ => (Finset.prod_mul_distrib).symm
  rw [h1, ← Fintype.prod_sum (fun (_ : Fin k) (i : Fin n) => v i * u i)]
  simp
