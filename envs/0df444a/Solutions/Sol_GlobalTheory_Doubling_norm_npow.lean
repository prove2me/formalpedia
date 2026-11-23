-- Prove2me | solution 1 for GlobalTheory.Doubling.norm_npow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:42.966654+00:00
-- url     : https://prove2.me/submissions/f1e201ab-d117-4db7-acfb-2920e7bc08d2

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
theorem _root_.solution {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : ‖npow r t‖ = (r : ℝ) ^ t.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hr t
end GlobalTheory.Doubling
