-- Prove2me | solution 1 for GlobalTheory.Doubling.npow_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:22.454798+00:00
-- url     : https://prove2.me/submissions/a9244d82-2ed7-45c6-8ef7-a0fe4658f348

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
theorem _root_.solution {r : ℝ≥0} (hr : 0 < r) (t t' : ℂ) : npow r (t + t') = npow r t * npow r t' :=
  Complex.cpow_add _ _ (by exact_mod_cast hr.ne')
end GlobalTheory.Doubling
