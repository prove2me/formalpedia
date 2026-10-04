-- Prove2me | solution 1 for Leopoldt.finiteIndex_closure_pow
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-02T19:40:13.77218+00:00
-- url     : https://prove2.me/submissions/8843f435-f946-460f-a234-3498c7427f62

import Theorems.Thm_Leopoldt_finiteIndex_closure_range_pow

/-- The closure of the `n`-th powers of a finite family generating a finite-index subgroup of
a commutative group has finite index: this is `Leopoldt.finiteIndex_closure_range_pow` with the
hypothesis `0 < n` in place of `n ≠ 0`. -/
theorem solution {G : Type*} [CommGroup G]
    {ι : Type*} [Finite ι] (u : ι → G)
    (hu : (Subgroup.closure (Set.range u)).FiniteIndex) (n : ℕ) (hn : 0 < n) :
    (Subgroup.closure (Set.range fun i : ι => u i ^ n)).FiniteIndex :=
  Leopoldt.finiteIndex_closure_range_pow G ι u hu n hn.ne'
