-- Prove2me | solution 1 for GlobalTheory.RootEx.FourierJacobiGroup.colE_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:15.51783+00:00
-- url     : https://prove2.me/submissions/ee45cf9c-29a9-4fb8-98f8-25491d1afdde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemFourierJacobiSubgroupIffParabolicMulColumn
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_colE_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.FourierJacobiGroup
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.FourierJacobiGroup
theorem _root_.solution (q : ℕ) (β : n → k) : (colE c q β)⁻¹ = colE c q (-β) :=
  inv_eq_of_mul_eq_one_right (QuotStep.colE_neg q β)
end GlobalTheory.RootEx.FourierJacobiGroup
