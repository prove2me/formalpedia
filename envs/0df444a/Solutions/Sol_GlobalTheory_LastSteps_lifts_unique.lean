-- Prove2me | solution 1 for GlobalTheory.LastSteps.lifts_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:36:24.515703+00:00
-- url     : https://prove2.me/submissions/3b4477b4-f1cc-4159-8a57-816f1c4bb740

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_dual_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
open GlobalTheory GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
variable [Fintype n] {L : Submodule 𝒪[k] (n → k)} {F : n → k}
namespace GlobalTheory.LastSteps
theorem _root_.solution {f g : Module.Dual 𝓀[k] (Red L)} (h : Lifts L F f) (h' : Lifts L F g) : f = g :=
  dual_ext fun z => by
    obtain ⟨s, hs, e⟩ := h z
    obtain ⟨t, ht, e'⟩ := h' z
    rw [← e, ← e', Subtype.ext (hs.trans ht.symm)]
end GlobalTheory.LastSteps
