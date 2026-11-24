-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.log_norm_eta_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:33:45.776132+00:00
-- url     : https://prove2.me/submissions/ac230faa-1516-4ad7-aac1-c22ef627425d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit
namespace GlobalTheory.KroneckerLimit
theorem _root_.solution (z : ℂ) (hz : 0 < z.im) :
    Real.log (‖ModularForm.eta z‖ ^ 2)
      = -(π * z.im / 6) + 2 * Real.log ‖∏' k : ℕ, (1 - ModularForm.eta_q k z)‖ := by
  rw [Real.log_pow, ModularForm.eta, norm_mul, Real.log_mul
    (norm_ne_zero_iff.2 (Function.Periodic.qParam_ne_zero _))
    (norm_ne_zero_iff.2 (ModularForm.eta_tprod_ne_zero hz)), Function.Periodic.norm_qParam,
    Real.log_exp]
  push_cast
  ring
end GlobalTheory.KroneckerLimit
