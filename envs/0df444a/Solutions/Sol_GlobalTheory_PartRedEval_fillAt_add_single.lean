-- Prove2me | solution 1 for GlobalTheory.PartRedEval.fillAt_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:37:00.162799+00:00
-- url     : https://prove2.me/submissions/9551ffa4-f25f-4e5b-9824-ce7fa4fe0c99

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
    (x : Matrix R Q k) (u : k) (y : I → k) :
    fillAt β E I (x + Matrix.single e.1 e.2 u) y = fillAt β E I x y + Matrix.single e.1 e.2 u := by
  ext r q
  by_cases h : e = (r, q)
  · subst h
    simp [fillAt, hE, hI]
  · have h0 : Matrix.single e.1 e.2 u r q = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ (fun h' => h (Prod.ext h'.1 h'.2))
    simp [fillAt, h0]
end GlobalTheory.PartRedEval
