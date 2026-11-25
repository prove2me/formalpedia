-- Prove2me | solution 1 for Newton.adjointAd.smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:17:20.154593+00:00
-- url     : https://prove2.me/submissions/97ea216d-78b6-4c58-be19-af0fb5f56062

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
import Theorems.Thm_Newton_SuNAlgebra_lie_def
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix



set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
open Newton.adjointAd
namespace Newton.adjointAd
theorem _root_.solution (A : SuNAlgebra N) (r : ℝ) (B : SuNAlgebra N) :
    adjointAd A (r • B) = r • adjointAd A B := by
  simp only [adjointAd]
  apply SuNAlgebra.ext
  simp only [SuNAlgebra.lie_def, SuNAlgebra.smul_matrix]
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
end Newton.adjointAd
