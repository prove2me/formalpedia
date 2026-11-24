-- Prove2me | solution 1 for GlobalTheory.LastSteps.inDual_of_lifts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:36:27.305796+00:00
-- url     : https://prove2.me/submissions/f915870a-42d7-4f31-ad71-5f56844306f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat

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
theorem _root_.solution {f : Module.Dual 𝓀[k] (Red L)} (h : Lifts L F f) : InDual L F := fun y hy => by
  obtain ⟨s, hs, -⟩ := h ⟨y, hy⟩
  exact hs ▸ s.2
end GlobalTheory.LastSteps
