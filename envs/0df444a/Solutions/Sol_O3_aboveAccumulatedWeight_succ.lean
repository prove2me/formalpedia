-- Prove2me | solution 1 for O3.aboveAccumulatedWeight_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:06:28.470806+00:00
-- url     : https://prove2.me/submissions/bafd61e2-e444-471f-9dea-7610bdfd157b

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {M : ℝ} (hM : M ≠ 0) (t : ℕ) :
    aboveAccumulatedWeight M (t + 1) =
      aboveAccumulatedWeight M t + aboveStepWeight M (t + 1) := by
  unfold aboveAccumulatedWeight aboveStepWeight
  push_cast
  field_simp [hM]
  ring
end O3
