-- Prove2me | solution 1 for GlobalTheory.exists_gl_det_eq_mul_eq_of_det_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:06.832953+00:00
-- url     : https://prove2.me/submissions/e3732527-20de-40ca-9be2-2415a1bc56b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumSingularAndInvertible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped TensorProduct Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k : Type) [Field k] (r : ℕ)
    (a : Matrix (Fin r) (Fin r) k) (ha : a.det = 0) (t : kˣ) :
    ∃ g : GL (Fin r) k, Matrix.GeneralLinearGroup.det g = t ∧
      a * (g : Matrix (Fin r) (Fin r) k) = a := by
  obtain ⟨v, hv, hav⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ha
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hi' : v i ≠ 0 := hi
  let w : Fin r → k := Pi.single i (((t : k) - 1) / v i)
  have hdet : (1 + Matrix.vecMulVec v w).det = (t : k) := by
    rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp only [w, single_dotProduct]
    field_simp
    ring
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + Matrix.vecMulVec v w)
    (by rw [hdet]; exact t.ne_zero), ?_, ?_⟩
  · ext
    exact hdet
  · change a * (1 + Matrix.vecMulVec v w) = a
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, hav]
    simp
end GlobalTheory
