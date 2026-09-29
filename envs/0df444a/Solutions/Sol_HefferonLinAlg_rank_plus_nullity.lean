-- Prove2me | solution 1 for HefferonLinAlg.rank_plus_nullity
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T15:43:19.150654+00:00
-- url     : https://prove2.me/submissions/3aa43352-3af3-4e90-9083-d27419ae4e6f

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

theorem solution
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.ker f) =
      Module.finrank K V := by
  exact f.finrank_range_add_finrank_ker
