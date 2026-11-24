-- Prove2me | solution 1 for GlobalTheory.HermLocal.Model.isQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:22:59.316478+00:00
-- url     : https://prove2.me/submissions/1237799a-505f-48f6-9edf-50a99f07543d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_SumSquaresNeThreeThreeAdic
import Theorems.Thm_GlobalTheory_QNorm_IsQuad_finrank_eq_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HermLocal
open GlobalTheory GlobalTheory.HermLocal GlobalTheory.HermLocal.Model
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]
namespace GlobalTheory.HermLocal.Model
theorem _root_.solution : Algebra.IsQuadraticExtension K (QuadraticAlgebra K d 0) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two d 0
end GlobalTheory.HermLocal.Model
