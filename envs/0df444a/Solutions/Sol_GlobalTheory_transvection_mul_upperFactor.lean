-- Prove2me | solution 1 for GlobalTheory.transvection_mul_upperFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:38:52.404585+00:00
-- url     : https://prove2.me/submissions/859fd6a0-fa71-4663-ae12-ba429c46f62b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
variable {k : Type} [Field k] {m : ℕ}
namespace GlobalTheory
theorem _root_.solution {i j : Fin m} (hji : j < i) {x : k} (hx : x ≠ 0) :
    transvection i j x * upperFactor i j x = swapLine i j x⁻¹ := by
  have hij : i ≠ j := ne_of_gt hji
  ext a b
  rw [transvection, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  by_cases ha : a = i
  · subst ha
    rw [single_mul_apply_same]
    by_cases hb : b = a
    · subst hb
      simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
        Function.update_apply, hij, hij.symm, hx]
    · by_cases hbj : b = j
      · subst hbj
        simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
          Function.update_apply, hij, hij.symm, hx]
      · simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
          Function.update_apply, hij, hij.symm, hx, hb, hbj, Ne.symm hb, Ne.symm hbj]
  · rw [single_mul_apply_of_ne _ _ _ _ _ ha, add_zero]
    by_cases haj : a = j
    · subst haj
      by_cases hb : b = a
      · subst hb
        simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
          Function.update_apply, hij, hij.symm, hx]
      · by_cases hbi : b = i
        · subst hbi
          simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
            Function.update_apply, hij, hij.symm, hx]
        · simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
            Function.update_apply, hij, hij.symm, hx, hb, hbi, Ne.symm hb, Ne.symm hbi]
    · simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
        Function.update_apply, hij, hij.symm, hx, ha, haj, Ne.symm ha, Ne.symm haj]
end GlobalTheory
