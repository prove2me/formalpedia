-- Prove2me | solution 1 for GlobalTheory.Doubling.npow_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:48.030454+00:00
-- url     : https://prove2.me/submissions/22525f72-22c5-4332-baed-d4671727034a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
namespace GlobalTheory.Doubling
theorem _root_.solution {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : npow r t = Complex.exp (Real.log r * t) := by
  rw [npow, Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.ofReal_log r.coe_nonneg]
end GlobalTheory.Doubling
