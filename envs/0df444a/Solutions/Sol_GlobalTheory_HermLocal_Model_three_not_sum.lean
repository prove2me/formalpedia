-- Prove2me | solution 1 for GlobalTheory.HermLocal.Model.three_not_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:50:11.299271+00:00
-- url     : https://prove2.me/submissions/bf37c4ce-2bfd-4ed3-b442-ac72ae7913d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_SumSquaresNeThreeThreeAdic
import Theorems.Thm_GlobalTheory_HermLocal_Model_sum_squares_ne_three_three_adic

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
namespace GlobalTheory.HermLocal.Model
theorem _root_.solution (x y : ℚ_[3]) : x ^ 2 + y ^ 2 ≠ 3 := by
  rcases le_total ‖y‖ ‖x‖ with h | h
  · exact sum_squares_ne_three_three_adic x y h
  · rw [add_comm]; exact sum_squares_ne_three_three_adic y x h
end GlobalTheory.HermLocal.Model
