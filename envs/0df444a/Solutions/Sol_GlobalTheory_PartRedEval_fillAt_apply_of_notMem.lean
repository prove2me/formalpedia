-- Prove2me | solution 1 for GlobalTheory.PartRedEval.fillAt_apply_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:36:37.226528+00:00
-- url     : https://prove2.me/submissions/9f725601-3493-4e3e-8a90-c6839ed03a83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRedEval
open GlobalTheory.PartRed
variable {k : Type} [Field k] {R Q : Type} [DecidableEq R] [DecidableEq Q]
namespace GlobalTheory.PartRedEval
theorem _root_.solution (β : Matrix R Q k) {E I : Finset (R × Q)} {e : R × Q} (hE : e ∉ E) (hI : e ∉ I)
    (x : Matrix R Q k) (y : I → k) : fillAt β E I x y e.1 e.2 = x e.1 e.2 := by
  simp [fillAt, hE, hI]
end GlobalTheory.PartRedEval
