-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.Model.neg_one_not_sq_sqrt_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:04.084243+00:00
-- url     : https://prove2.me/submissions/97557615-9834-44c8-be21-6ad19a9cf008

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_NegOneNotSqSqrtTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory.QuadSymbol
open GlobalTheory GlobalTheory.QuadSymbol GlobalTheory.QuadSymbol.Model
namespace GlobalTheory.QuadSymbol.Model
theorem _root_.solution (r : QuadraticAlgebra ℚ 2 0) : r ^ 2 ≠ -1 + 0 * r := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  simp [pow_two, QuadraticAlgebra.re_one] at this
  nlinarith [mul_self_nonneg r.re, mul_self_nonneg r.im]
end GlobalTheory.QuadSymbol.Model
