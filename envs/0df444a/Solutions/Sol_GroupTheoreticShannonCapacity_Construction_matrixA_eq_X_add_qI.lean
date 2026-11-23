-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.matrixA_eq_X_add_qI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:32:52.96799+00:00
-- url     : https://prove2.me/submissions/7c532cda-4360-4512-adf2-31338466c145

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (k b r s : ℤ) :
    ((matrixA n k b r s).map (↑· : ℚ → ℝ)) =
    ((matrixX n k b r s).map (↑· : ℚ → ℝ)) + (q n k b r s : ℝ) • 1 := by
  simp only [matrixA]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
             Matrix.one_apply, smul_eq_mul, Rat.cast_add, Rat.cast_mul]
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte, mul_one]; ring
  · simp only [hij, ↓reduceIte, Rat.cast_zero, mul_zero, zero_add, add_zero]
end GroupTheoreticShannonCapacity.Construction
