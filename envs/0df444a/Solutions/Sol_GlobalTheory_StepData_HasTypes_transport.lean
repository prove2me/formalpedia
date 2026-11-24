-- Prove2me | solution 1 for GlobalTheory.StepData.HasTypes.transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:07.780601+00:00
-- url     : https://prove2.me/submissions/7e0c9a95-9673-4db5-b0d4-842c800da782

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_LatFrame_om_transport

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
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.StepData
namespace HasTypes
theorem _root_.solution {Y Y' : Type*} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {μ : kˣ →* ℂˣ}
    {P' : Level (GL a k)} {P : Level (GL b k)} {Φ : Matrix b a k → ℂ} (H : HasTypes μ P' P Φ)
    (F : LatFrame k b Y) (F' : LatFrame k a Y') :
    HasTypes μ (P'.map F'.conj) (P.map F.conj) (F.transport F' Φ) := by
  refine ⟨fun g => ?_, fun h => ?_⟩
  · have := F.om_transport F' μ (F'.conj.symm g) 1 Φ
    rw [MulEquiv.apply_symm_apply, map_one] at this
    exact this.trans (congrArg (F.transport F') (H.1 ⟨_, g.2⟩))
  · have := F.om_transport F' μ 1 (F.conj.symm h) Φ
    rw [MulEquiv.apply_symm_apply, map_one] at this
    exact this.trans (congrArg (F.transport F') (H.2 ⟨_, h.2⟩))
end HasTypes
end GlobalTheory.StepData
