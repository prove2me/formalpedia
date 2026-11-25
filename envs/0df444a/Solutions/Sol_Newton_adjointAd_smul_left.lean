-- Prove2me | solution 1 for Newton.adjointAd_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:17:58.476006+00:00
-- url     : https://prove2.me/submissions/57430eb0-222f-46d5-a16c-db62098102b7

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
import Theorems.Thm_Newton_adjointAd_zero
import Theorems.Thm_Newton_adjointAd_zero_left
import Theorems.Thm_Newton_adjointAd_self
import Theorems.Thm_Newton_SuNAlgebra_lie_def
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix


attribute [local simp] Newton.adjointAd.zero
attribute [local simp] Newton.adjointAd.zero_left
attribute [local simp] Newton.adjointAd.self

set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
namespace Newton
theorem _root_.solution (r : ℝ) (A B : SuNAlgebra N) :
    adjointAd (r • A) B = r • adjointAd A B := by
  simp only [adjointAd]
  apply SuNAlgebra.ext
  simp only [SuNAlgebra.lie_def, SuNAlgebra.smul_matrix]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
end Newton
