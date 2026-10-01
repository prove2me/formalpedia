-- Prove2me | solution 1 for GrothendieckConstant.opt_le_sdp
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:42:48.58601+00:00
-- url     : https://prove2.me/submissions/9496a32b-f15c-49d5-9956-dc3ae826e71a

import Mathlib
import Definitions.Def_GrothendieckConstantDefs

open GrothendieckConstant

theorem solution (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    optValue A ≤ sdpValue A := by
  have limitado : BddAbove (sdpSet A) := by
    refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
    rintro s ⟨d, u, v, hu, hv, rfl⟩
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    calc
      A i j * inner ℝ (u i) (v j) ≤ |A i j * inner ℝ (u i) (v j)| := le_abs_self _
      _ = |A i j| * |inner ℝ (u i) (v j)| := abs_mul _ _
      _ ≤ |A i j| * 1 := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        simpa [hu i, hv j] using (abs_real_inner_le_norm (u i) (v j))
      _ = |A i j| := mul_one _
  have nao_vazio : (optSet A).Nonempty := by
    refine ⟨∑ i, ∑ j, A i j * 1 * 1, ?_⟩
    exact ⟨fun _ => 1, fun _ => 1, fun _ => Or.inl rfl, fun _ => Or.inl rfl, rfl⟩
  apply csSup_le_csSup limitado nao_vazio
  rintro s ⟨x, y, hx, hy, rfl⟩
  refine ⟨1, (fun i => EuclideanSpace.single 0 (x i)),
    (fun j => EuclideanSpace.single 0 (y j)), ?_, ?_, ?_⟩
  · intro i
    rcases hx i with h | h <;> simp [h]
  · intro j
    rcases hy j with h | h <;> simp [h]
  · simp [EuclideanSpace.inner_single_left, mul_left_comm, mul_comm]
