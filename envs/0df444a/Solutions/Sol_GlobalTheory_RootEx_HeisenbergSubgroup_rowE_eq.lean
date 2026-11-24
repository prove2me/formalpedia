-- Prove2me | solution 1 for GlobalTheory.RootEx.HeisenbergSubgroup.rowE_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:06.9736+00:00
-- url     : https://prove2.me/submissions/42723624-d85b-40aa-9475-d1c78ad1f07b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsHeisenbergSubgroupFourierJacobiCommutator
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_rowE_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.HeisenbergSubgroup
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.HeisenbergSubgroup
theorem _root_.solution (u : n → k) : (rowE c p u).val = hM c p u 0 0 := by
  rw [ExchangeSupport.rowE_val, hM, col_zero, zM_zero, add_zero]
end GlobalTheory.RootEx.HeisenbergSubgroup
