-- Prove2me | solution 1 for GlobalTheory.TraceDualMin.cc_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:59.704683+00:00
-- url     : https://prove2.me/submissions/a29c5a99-c392-4f08-84fa-4c0fae31565e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.TraceDualMin
namespace GlobalTheory.TraceDualMin
theorem _root_.solution (a : E) : cc (cc a) = a := by
  simp [cc]
end GlobalTheory.TraceDualMin
