-- Prove2me | solution 1 for GlobalTheory.FormalLog.coeff_prim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:14.702093+00:00
-- url     : https://prove2.me/submissions/f54514ff-f71c-4266-a8b2-d6f6b0f71a3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim

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
theorem _root_.solution (ω : τ → MvPowerSeries τ k) (m : τ →₀ ℕ) :
    coeff m (prim ω) = algebraMap ℚ k ((m.degree : ℚ)⁻¹) *
      ∑ w, if m w = 0 then 0 else coeff (m - Finsupp.single w 1) (ω w) := rfl
end GlobalTheory.FormalLog
