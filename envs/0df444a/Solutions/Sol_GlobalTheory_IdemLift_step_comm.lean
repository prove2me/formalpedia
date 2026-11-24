-- Prove2me | solution 1 for GlobalTheory.IdemLift.step_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:38:34.359812+00:00
-- url     : https://prove2.me/submissions/58f18f7f-44ce-452b-b322-29076b2d5c70

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
theorem _root_.solution {y N : Matrix (Fin n) (Fin n) E} (h : y * N = N * y) :
    step y * N = N * step y := by
  have hc : Commute y N := h
  have h2 := hc.mul_left hc
  have h3 := h2.mul_left hc
  exact ((h2.add_left h2).add_left h2).sub_left (h3.add_left h3)
end GlobalTheory.IdemLift
