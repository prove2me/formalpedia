-- Prove2me | solution 1 for OAI.PiExponent.InterpolationMatrix.prod_add_pow_fin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:53:24.081983+00:00
-- url     : https://prove2.me/submissions/e25cdace-ec47-4e4f-a2f0-245eee2e5200

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators


theorem solution
    {R : Type*} [CommSemiring R] {m : ℕ}
    (x y : Fin m → R) (k : Fin m → ℕ) :
    (∏ i, (x i + y i) ^ k i) =
      ∑ u : (∀ i : Fin m, Fin (k i + 1)),
        ((∏ i, (k i).choose (u i : ℕ) : ℕ) : R) *
          (∏ i, x i ^ (k i - (u i : ℕ))) *
          ∏ i, y i ^ (u i : ℕ) := by
  have h1 : ∀ i, (x i + y i) ^ k i = ∑ u : Fin (k i + 1),
      ((k i).choose (u : ℕ) : R) * x i ^ (k i - (u : ℕ)) * y i ^ (u : ℕ) := by
    intro i
    rw [add_comm, add_pow, Fin.sum_univ_eq_sum_range (fun u => ((k i).choose u : R) * x i ^ (k i - u) * y i ^ u)]
    refine Finset.sum_congr rfl (fun u _ => by ring)
  simp_rw [h1]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Nat.cast_prod]

