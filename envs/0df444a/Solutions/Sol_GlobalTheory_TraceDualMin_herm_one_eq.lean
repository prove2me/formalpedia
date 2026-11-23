-- Prove2me | solution 1 for GlobalTheory.TraceDualMin.herm_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:38.494749+00:00
-- url     : https://prove2.me/submissions/4f07d019-ff1b-4510-985d-82fce004736c

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
theorem _root_.solution {n : ℕ} (x y : Fin n → E) : herm 1 x y = ∑ k, x k * cc (y k) := by
  simp [herm, Matrix.one_apply]
end GlobalTheory.TraceDualMin
