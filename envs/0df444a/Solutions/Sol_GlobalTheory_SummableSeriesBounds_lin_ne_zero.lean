-- Prove2me | solution 1 for GlobalTheory.SummableSeriesBounds.lin_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:58:50.143801+00:00
-- url     : https://prove2.me/submissions/9794cafa-5ae5-4ec2-8ea4-159f28fdd409

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableSeriesBounds
open PowerSeries Filter Topology
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
namespace GlobalTheory.SummableSeriesBounds
theorem _root_.solution (π : C) : lin π ≠ 0 := by
  intro h
  have := congrArg (fun Φ : bdd C => coeff 1 (Φ : PowerSeries C)) h
  simp [lin, coeff_C, coeff_X] at this
end GlobalTheory.SummableSeriesBounds
