-- Prove2me | solution 1 for LLLFactor.Reduction.gram_eq_prod_gs
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:02:01.78635+00:00
-- url     : https://prove2.me/submissions/bdfaf8bc-d42d-44ab-91b5-b5cbbb18791e

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

set_option backward.isDefEq.respectTransparency false
open LLLFactor.Reduction LLLFactor.RedBasis
open scoped InnerProductSpace

private theorem prefix_expansion {n i : ℕ} (b : Fin n → Vec n) (hi : i ≤ n) (j : Fin i) :
    b (Fin.castLE hi j) = gs b (Fin.castLE hi j) +
      ∑ l : Fin i, if l < j then mu b (Fin.castLE hi j) (Fin.castLE hi l) •
        gs b (Fin.castLE hi l) else 0 := by
  have h := InnerProductSpace.gramSchmidt_def'' ℝ b (Fin.castLE hi j)
  have he : (∑ l : Fin i, if l < j then mu b (Fin.castLE hi j) (Fin.castLE hi l) •
      gs b (Fin.castLE hi l) else 0) =
      ∑ l ∈ Finset.Iio (Fin.castLE hi j), mu b (Fin.castLE hi j) l • gs b l := by
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun l _ => Fin.castLE hi l)
    · intro l hl
      simpa using (Finset.mem_filter.mp hl).2
    · intro a ha c hc hac
      exact Fin.ext (congrArg (@Fin.val n) hac)
    · intro l hl
      have hl0 : l < Fin.castLE hi j := Finset.mem_Iio.mp hl
      have hl' : l.val < j.val := hl0
      refine ⟨⟨l.val, by omega⟩, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'⟩
      · exact Fin.ext rfl
    · intro l hl
      rfl
  rw [he]
  simpa [gs, mu, real_inner_comm, real_inner_self_eq_norm_sq] using h

private theorem prefix_gram {n i : ℕ} (b : Fin n → Vec n) (hi : i ≤ n) :
    gram b i = ∏ j : Fin i, ‖gs b (Fin.castLE hi j)‖ ^ 2 := by
  let v := fun j : Fin i => b (Fin.castLE hi j)
  let w := fun j : Fin i => gs b (Fin.castLE hi j)
  let C : Matrix (Fin i) (Fin i) ℝ := fun j l =>
    if j = l then 1 else if l < j then mu b (Fin.castLE hi j) (Fin.castLE hi l) else 0
  have hv (j : Fin i) : v j = ∑ l, C j l • w l := by
    rw [show (∑ l, C j l • w l) = w j +
        ∑ l : Fin i, if l < j then mu b (Fin.castLE hi j) (Fin.castLE hi l) • w l else 0 by
      calc
        _ = ∑ l, ((if l = j then w l else 0) +
            (if l < j then mu b (Fin.castLE hi j) (Fin.castLE hi l) • w l else 0)) := by
          apply Finset.sum_congr rfl
          intro l hl
          by_cases he : j = l
          · subst l; simp [C]
          · simp [C, he, Ne.symm he]
        _ = _ := by rw [Finset.sum_add_distrib]; simp]
    exact prefix_expansion b hi j
  have hw : Matrix.gram ℝ w = Matrix.diagonal (fun j => ‖w j‖ ^ 2) := by
    ext j l
    by_cases h : j = l
    · subst l
      simp [real_inner_self_eq_norm_sq]
    · simp only [Matrix.gram_apply, Matrix.diagonal_apply_ne _ h]
      exact InnerProductSpace.gramSchmidt_orthogonal ℝ b (by
        intro he; apply h; exact Fin.ext (congrArg (@Fin.val n) he))
  have hC : C.IsLowerTriangular := by
    intro j l h
    change j < l at h
    simp [C, ne_of_lt h, not_lt_of_ge h.le]
  have hd : C.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular C hC]
    simp [C]
  have hm : Matrix.gram ℝ v = C * Matrix.gram ℝ w * C.transpose := by
    ext j l
    rw [Matrix.gram_apply, hv j, hv l]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.gram_apply]
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  unfold gram
  rw [dif_pos hi]
  change (Matrix.gram ℝ v).det = _
  rw [hm, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hd, one_mul, mul_one, hw,
    Matrix.det_diagonal]

theorem solution {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b) :
    (∀ (i : ℕ) (hi : i ≤ n),
      gram b i = ∏ j : Fin i, ‖gs b (Fin.castLE hi j)‖ ^ 2 ∧ 0 < gram b i) ∧
    gram b 0 = 1 ∧ gram b n = latticeDet b ^ 2 := by
  constructor
  · intro i hi
    refine ⟨prefix_gram b hi, ?_⟩
    rw [prefix_gram b hi]
    apply Finset.prod_pos
    intro j hj
    exact pow_pos (norm_pos_iff.mpr (InnerProductSpace.gramSchmidt_ne_zero _ hb)) _
  · constructor
    · simp [gram]
    · let B : Matrix (Fin n) (Fin n) ℝ := fun i j => b j i
      have hB : Matrix.gram ℝ b = B.transpose * B := by
        ext i j
        simp [B, Matrix.gram, Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
      simp only [gram, dif_pos (le_refl n), latticeDet]
      change (Matrix.gram ℝ b).det = |B.det| ^ 2
      rw [hB, Matrix.det_mul, Matrix.det_transpose, sq_abs]
      ring

#print axioms solution
