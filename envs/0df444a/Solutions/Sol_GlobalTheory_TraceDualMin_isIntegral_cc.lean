-- Prove2me | solution 1 for GlobalTheory.TraceDualMin.isIntegral_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:06.35592+00:00
-- url     : https://prove2.me/submissions/b2b10864-c6ee-4f3d-84f0-6b46b12753c2

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
theorem _root_.solution {a : E} (ha : IsIntegral ℤ a) : IsIntegral ℤ (cc a) :=
  ha.map ((IsCMField.complexConj E).restrictScalars ℤ).toAlgHom
end GlobalTheory.TraceDualMin
