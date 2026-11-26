-- Prove2me | solution 1 for O3.aboveInitialLevel_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:43.274803+00:00
-- url     : https://prove2.me/submissions/dc19edea-3d78-4afb-8cbf-408f225e66d2

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {M D : ℝ} (hM : 0 < M) (hD : 0 < D) :
    0 < aboveInitialLevel M D := by
  exact mul_pos hM (sq_pos_of_pos hD)
end O3
