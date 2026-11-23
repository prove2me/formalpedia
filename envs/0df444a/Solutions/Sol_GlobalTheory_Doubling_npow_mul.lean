-- Prove2me | solution 1 for GlobalTheory.Doubling.npow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:38.640388+00:00
-- url     : https://prove2.me/submissions/30074757-009f-49a7-a186-88ac174c1d7d

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
theorem _root_.solution (r r' : ℝ≥0) (t : ℂ) : npow (r * r') t = npow r t * npow r' t := by
  rw [npow, NNReal.coe_mul, Complex.ofReal_mul]; exact Complex.mul_cpow_ofReal_nonneg r.2 r'.2 t
end GlobalTheory.Doubling
