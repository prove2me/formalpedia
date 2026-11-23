-- Prove2me | solution 1 for GlobalTheory.FormalLog.constantCoeff_prim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:25.454342+00:00
-- url     : https://prove2.me/submissions/0d1f34f1-9347-40da-ba38-c08b2def40d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
import Theorems.Thm_GlobalTheory_FormalLog_coeff_prim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [Fintype τ] [DecidableEq τ]
namespace GlobalTheory.FormalLog
theorem _root_.solution (ω : τ → MvPowerSeries τ k) : constantCoeff (prim ω) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_prim]
  simp
end GlobalTheory.FormalLog
