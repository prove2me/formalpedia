-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.discr_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:45:09.547516+00:00
-- url     : https://prove2.me/submissions/a59a6569-d6f5-40c5-8370-e0e339ead781

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Theorems.Thm_GlobalTheory_QuadraticZeta_repr_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {R : Type*} [CommRing R]
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (b : Basis (Fin 2) ℤ R) (h0 : b 0 = 1) {t n : ℤ} (hw : b 1 ^ 2 = t * b 1 - n) :
    Algebra.discr ℤ b = t ^ 2 - 4 * n := by
  have tr : ∀ x y : ℤ, Algebra.trace ℤ R (x + y * b 1) = 2 * x + y * t := by
    intro x y
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul, h0, mul_one, (repr_coord b h0 x y).1,
      show (x + y * b 1 : R) * b 1 = (-(y * n) : ℤ) + (x + y * t : ℤ) * b 1 by
        push_cast; linear_combination (y : R) * hw, (repr_coord b h0 _ _).2]
    ring
  have t1 := tr 1 0
  have t2 := tr 0 1
  have t3 := tr (-n) t
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, h0, mul_one, one_mul]
  rw [show b 1 * b 1 = (-n : ℤ) + t * b 1 by push_cast; linear_combination hw, t3]
  simp only [Int.cast_one, Int.cast_zero, zero_mul, add_zero, one_mul, zero_add] at t1 t2
  rw [t1, t2]
  ring
end GlobalTheory.QuadraticZeta
