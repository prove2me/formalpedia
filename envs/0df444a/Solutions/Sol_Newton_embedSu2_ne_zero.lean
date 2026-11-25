-- Prove2me | solution 1 for Newton.embedSu2_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:03:36.492098+00:00
-- url     : https://prove2.me/submissions/62158753-f7a2-455e-a277-2ca4d7b542aa

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix



set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution (A : SuNAlgebra 2) (hA : A ≠ 0) (N : ℕ) :
    embedSu2 A N ≠ 0 := by
  intro h
  apply hA
  apply SuNAlgebra.ext
  have hM := congr_arg SuNAlgebra.matrix h
  simp only [embedSu2, SuNAlgebra.zero_matrix] at hM
  ext i j
  have hi : i.val < 2 := i.isLt
  have hj : j.val < 2 := j.isLt
  have hij : (embedMatrix2 A.matrix N) ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ = 0 := by
    rw [hM]; rfl
  simp only [embedMatrix2, hi, hj, dite_true] at hij
  rw [SuNAlgebra.zero_matrix, Matrix.zero_apply]
  exact hij
end Newton
