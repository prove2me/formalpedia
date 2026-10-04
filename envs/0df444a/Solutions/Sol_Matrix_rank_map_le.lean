-- Prove2me | solution 1 for Matrix.rank_map_le
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T09:00:24.853973+00:00
-- url     : https://prove2.me/submissions/3da96182-55b6-480d-b5a3-b49f3c76f511

import Mathlib

open Module Submodule

theorem solution {m n : Type*} [Fintype n] {F F' : Type*} [Field F] [Field F']
    (ι : F →+* F') (A : Matrix m n F) : (A.map ι).rank ≤ A.rank := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  set S := span F (Set.range A.col) with hS
  have : FiniteDimensional F S := FiniteDimensional.span_of_finite F (Set.finite_range _)
  let b := Module.finBasis F S
  let w : Fin (finrank F S) → (m → F') := fun k i => ι ((b k : m → F) i)
  have hmem : ∀ j, (A.map ι).col j ∈ span F' (Set.range w) := by
    intro j
    have hj : A.col j ∈ S := subset_span ⟨j, rfl⟩
    have hsum := b.sum_repr ⟨A.col j, hj⟩
    have hcol : A.col j = ∑ k, (b.repr ⟨A.col j, hj⟩ k) • (b k : m → F) := by
      have := congrArg Subtype.val hsum
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    have : (A.map ι).col j = ∑ k, ι (b.repr ⟨A.col j, hj⟩ k) • w k := by
      funext i
      have := congrFun hcol i
      simp only [Matrix.col_apply, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, w] at this ⊢
      rw [this, map_sum]
      simp [map_mul]
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (subset_span ⟨k, rfl⟩)
  have : FiniteDimensional F' (span F' (Set.range w)) :=
    FiniteDimensional.span_of_finite F' (Set.finite_range _)
  calc finrank F' (span F' (Set.range (A.map ι).col))
      ≤ finrank F' (span F' (Set.range w)) :=
        Submodule.finrank_mono (span_le.2 (by rintro _ ⟨j, rfl⟩; exact hmem j))
    _ ≤ Fintype.card (Fin (finrank F S)) := finrank_range_le_card w
    _ = finrank F S := Fintype.card_fin _
