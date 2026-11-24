-- Prove2me | solution 1 for GlobalTheory.HermModel.eq_zero_of_trace_mul_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:29:16.491739+00:00
-- url     : https://prove2.me/submissions/dafb2337-3933-40a9-a62b-ac214e778ebe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermModel
variable {E : Type} [Field E] [NumberField E]
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.HermModel
namespace _root_.GlobalTheory.HermModel
theorem _root_.solution {t : E}
    (ht : ∀ a : 𝓞 E, Algebra.trace ℚ E (t * a) = 0) : t = 0 := by
  classical
  have h0 : Algebra.traceForm ℚ E t = 0 := (NumberField.integralBasis E).ext fun i => by
    rw [NumberField.integralBasis_apply, Algebra.traceForm_apply, LinearMap.zero_apply]
    exact ht _
  exact (traceForm_nondegenerate ℚ E).1 t fun y => by rw [h0]; rfl
end _root_.GlobalTheory.HermModel
end GlobalTheory.HermModel
