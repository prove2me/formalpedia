-- Prove2me | solution 1 for GlobalTheory.PeriodSymm.antiRow_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:32:13.658185+00:00
-- url     : https://prove2.me/submissions/376e4429-dfdc-4b36-a4ed-e870d5159204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SetIntegralFderivEqZeroOfLatticePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open Filter Topology
open GlobalTheory GlobalTheory.PeriodSymm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.PeriodSymm
theorem _root_.solution {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (m : Fin g) (z : Fin g → ℂ) :
    antiRow M m z = M.mulVec (star z) m := rfl
end GlobalTheory.PeriodSymm
