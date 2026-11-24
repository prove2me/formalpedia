-- Prove2me | solution 1 for GlobalTheory.PeriodSymm.antiRow_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:23:03.703803+00:00
-- url     : https://prove2.me/submissions/d2ed3e0b-8ec8-4f67-80cc-868eeca22a25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SetIntegralFderivEqZeroOfLatticePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSections
import Theorems.Thm_GlobalTheory_PeriodSymm_antiRow_apply

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
    antiRow M m (I • z) = -I * antiRow M m z := by
  rw [antiRow_apply, antiRow_apply, star_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  simp [Complex.star_def]
end GlobalTheory.PeriodSymm
