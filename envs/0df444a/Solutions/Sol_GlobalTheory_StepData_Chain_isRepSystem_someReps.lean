-- Prove2me | solution 1 for GlobalTheory.StepData.Chain.isRepSystem_someReps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:11:23.999959+00:00
-- url     : https://prove2.me/submissions/2ff0faa7-7f3b-4120-94fe-8dcce87ebdb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s : ℕ} {X : ℕ → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type*} [Fintype Z] [DecidableEq Z]
open GlobalTheory.StepData.Chain
variable (T : Chain k s X Z)
variable (A : RepFam k s X)
variable (S M : Submodule 𝒪[k] (X (s + 1) → k))
variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
omit [BorelSpace k]
namespace GlobalTheory.StepData.Chain
theorem _root_.solution : T.IsRepSystem (T.someReps ψ ν) ψ ν := by
  refine ⟨fun _ _ => rfl, fun j c h => ⟨?_, ?_, fun β hβ => ⟨_, ⟨β, hβ, rfl⟩, DoubleCoset.out_eq' _ _ β⟩⟩⟩
  · rintro _ ⟨β, hβ, rfl⟩
    exact (DoubleCoset.out_eq' _ _ β).symm ▸ hβ
  · rintro _ ⟨β, -, rfl⟩ _ ⟨β', -, rfl⟩ e
    exact congrArg _ ((DoubleCoset.out_eq' _ _ β).symm.trans (e.trans (DoubleCoset.out_eq' _ _ β')))
end GlobalTheory.StepData.Chain
