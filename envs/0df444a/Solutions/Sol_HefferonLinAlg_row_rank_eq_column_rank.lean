-- Prove2me | solution 1 for HefferonLinAlg.row_rank_eq_column_rank
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T15:48:13.920209+00:00
-- url     : https://prove2.me/submissions/afd2f6c8-3ce6-4959-9f11-10536950780f

import Mathlib.LinearAlgebra.Matrix.Rank

open Matrix

theorem solution
    {K : Type*} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) :
    Module.finrank K (Submodule.span K (Set.range A)) =
      Module.finrank K (Submodule.span K (Set.range Aᵀ)) := by
  change Module.finrank K (Submodule.span K (Set.range A.row)) =
    Module.finrank K (Submodule.span K (Set.range Aᵀ.row))
  rw [← Matrix.rank_eq_finrank_span_row A,
    ← Matrix.rank_eq_finrank_span_row Aᵀ, Matrix.rank_transpose]
