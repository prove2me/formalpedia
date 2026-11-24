-- Prove2me | solution 1 for GlobalTheory.PeriodicCousin.antilin_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:51.471795+00:00
-- url     : https://prove2.me/submissions/d0837892-e490-4c9f-965b-49cd88936551

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DbarSolveComplexTorusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicPeriodicCocycleCoboundary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real Topology
open GlobalTheory GlobalTheory.PeriodicCousin
variable {g : ℕ}
namespace GlobalTheory.PeriodicCousin
theorem _root_.solution (t z : Fin g → ℂ) : antilin t z = t ⬝ᵥ star z := by
  simp [antilin, dotProduct]
end GlobalTheory.PeriodicCousin
