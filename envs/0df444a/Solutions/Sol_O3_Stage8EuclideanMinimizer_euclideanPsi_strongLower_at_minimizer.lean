-- Prove2me | solution 1 for O3.Stage8EuclideanMinimizer.euclideanPsi_strongLower_at_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:27:39.290163+00:00
-- url     : https://prove2.me/submissions/09acd416-e688-4c23-9cf6-2fe08621c74d

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
    euclideanPsi M x₀ s c x ≥
      euclideanPsi M x₀ s c (euclideanPsiMinimizer M x₀ s) +
        M / 2 *
          (lpNorm 2 (x - euclideanPsiMinimizer M x₀ s)) ^ (2 : ℕ) := by
  exact (euclideanPsi_eq_min_add_sq hM.ne' x₀ s c x).ge
end O3.Stage8EuclideanMinimizer
