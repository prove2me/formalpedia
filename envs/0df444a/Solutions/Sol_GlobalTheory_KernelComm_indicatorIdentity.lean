-- Prove2me | solution 1 for GlobalTheory.KernelComm.indicatorIdentity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:32:59.830079+00:00
-- url     : https://prove2.me/submissions/a20d1b28-5e7b-4a90-a29d-413aaaee6695

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_KernelComm_sum_target
import Theorems.Thm_GlobalTheory_KernelComm_sum_source

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp
noncomputable section
open GlobalTheory GlobalTheory.KernelComm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
namespace GlobalTheory.KernelComm
theorem _root_.solution : IndicatorIdentity := fun _ _ _ _ _ _ _ _ _ q _ _ he Q x =>
  ⟨sum_target q he Q x, sum_source q he Q x⟩
end GlobalTheory.KernelComm
