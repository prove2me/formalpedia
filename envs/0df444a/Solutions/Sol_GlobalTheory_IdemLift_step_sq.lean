-- Prove2me | solution 1 for GlobalTheory.IdemLift.step_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:38:35.72225+00:00
-- url     : https://prove2.me/submissions/f125e868-134f-4dfc-aa1e-31505d1db48c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralIdempotentLiftNewton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.IdemLift
open Filter Topology
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
namespace GlobalTheory.IdemLift
theorem _root_.solution (y : Matrix (Fin n) (Fin n) E) :
    step y * step y - step y = (y * y - y) * (y * y - y) *
      ((y * y - y) + (y * y - y) + (y * y - y) + (y * y - y) - (1 + 1 + 1)) := by
  unfold step; noncomm_ring
end GlobalTheory.IdemLift
