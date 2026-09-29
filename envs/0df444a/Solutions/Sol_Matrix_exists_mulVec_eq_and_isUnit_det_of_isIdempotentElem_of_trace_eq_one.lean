-- Prove2me | solution 1 for Matrix.exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/cdf79d20-e6a6-5dc4-b30b-08606682d66d

import Mathlib
import Theorems.Thm_Matrix_det_eq_zero_of_isIdempotentElem_of_trace_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one

set_option autoImplicit false

universe u

theorem solution {A : Type u} [CommRing A] [IsLocalRing A]
    {e : Matrix (Fin 2) (Fin 2) A} (he : e * e = e) (htr : e.trace = 1) :
    ∃ u w : Fin 2 → A, IsUnit (Matrix.of (fun i j => ![u, w] j i)).det ∧
      e.mulVec u = u ∧ e.mulVec w = 0 := by
  have hdet : e.det = 0 := Matrix.det_eq_zero_of_isIdempotentElem_of_trace_eq_one he htr
  have hdet' : e 0 0 * e 1 1 - e 0 1 * e 1 0 = 0 := by rw [← Matrix.det_fin_two]; exact hdet
  have htr' : e 0 0 + e 1 1 = 1 := by rw [← Matrix.trace_fin_two]; exact htr

  have hee : ∀ i j, (e * e) i j = e i j := fun i j => by rw [he]

  rcases IsLocalRing.isUnit_or_isUnit_of_add_one htr' with h00 | h11
  ·
    refine ⟨fun i => e i 0, fun i => (1 - e) i 1, ?_, ?_, ?_⟩
    · have : (Matrix.of (fun i j => ![(fun i => e i 0), (fun i => (1 - e) i 1)] j i)).det = e 0 0 := by
        rw [Matrix.det_fin_two]
        simp [Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply]
        linear_combination (-1 : A) * hdet'
      rw [this]; exact h00
    · ext i
      have := hee i 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two] at this
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, this]
    · ext i
      have h := hee i 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply, mul_sub]
      fin_cases i <;> simp at h ⊢ <;> linear_combination (-1 : A) * h
  ·
    refine ⟨fun i => e i 1, fun i => (1 - e) i 0, ?_, ?_, ?_⟩
    · have : (Matrix.of (fun i j => ![(fun i => e i 1), (fun i => (1 - e) i 0)] j i)).det = - e 1 1 := by
        rw [Matrix.det_fin_two]
        simp [Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply]
        linear_combination hdet'
      rw [this]; exact h11.neg
    · ext i
      have := hee i 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two] at this
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, this]
    · ext i
      have h := hee i 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply, mul_sub]
      fin_cases i <;> simp at h ⊢ <;> linear_combination (-1 : A) * h

end S_Matrix_exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one
end P2MW
export P2MW.S_Matrix_exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one (solution)
