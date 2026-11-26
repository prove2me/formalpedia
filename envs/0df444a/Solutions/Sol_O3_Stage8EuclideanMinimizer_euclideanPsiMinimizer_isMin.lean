-- Prove2me | solution 1 for O3.Stage8EuclideanMinimizer.euclideanPsiMinimizer_isMin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:27:41.181776+00:00
-- url     : https://prove2.me/submissions/8e820c87-d140-4469-ac3a-5b016809aa31

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage8EuclideanMinimizer
import Theorems.Thm_O3_Stage8EuclideanMinimizer_euclideanPsi_eq_min_add_sq

set_option autoImplicit true
open O3
open O3.Stage8EuclideanMinimizer
namespace O3.Stage8EuclideanMinimizer
theorem _root_.solution {M : ℝ} (hM : 0 < M) {d : ℕ}
    (x₀ s : Point d) (c : ℝ) (x : Point d) :
    euclideanPsi M x₀ s c (euclideanPsiMinimizer M x₀ s) ≤
      euclideanPsi M x₀ s c x := by
  have hsquare : 0 ≤
      (lpNorm 2 (x - euclideanPsiMinimizer M x₀ s)) ^ (2 : ℕ) := sq_nonneg _
  have hcoef : 0 ≤ M / 2 := div_nonneg hM.le (by norm_num)
  have heq := euclideanPsi_eq_min_add_sq hM.ne' x₀ s c x
  calc
    euclideanPsi M x₀ s c (euclideanPsiMinimizer M x₀ s) ≤
        euclideanPsi M x₀ s c (euclideanPsiMinimizer M x₀ s) +
          M / 2 *
            (lpNorm 2 (x - euclideanPsiMinimizer M x₀ s)) ^ (2 : ℕ) :=
      le_add_of_nonneg_right (mul_nonneg hcoef hsquare)
    _ = euclideanPsi M x₀ s c x := heq.symm
end O3.Stage8EuclideanMinimizer
