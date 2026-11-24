-- Prove2me | solution 1 for GlobalTheory.StepData.LatFrame.om_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:26:06.533893+00:00
-- url     : https://prove2.me/submissions/d305f009-12f9-4ebb-9d98-f34840ae731c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_LatFrame_det_conj
import Theorems.Thm_GlobalTheory_StepData_LatFrame_coords_mul

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
variable {ι ι' Y Y' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
open GlobalTheory.StepData.LatFrame
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.StepData.LatFrame
theorem _root_.solution (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (μ : kˣ →* ℂˣ) (g : GL ι' k) (h : GL ι k)
    (Φ : Matrix ι ι' k → ℂ) :
    om μ (F'.conj g) (F.conj h) (F.transport F' Φ) = F.transport F' (om μ g h Φ) := by
  funext x
  simp only [om, transport, det_conj, ← Fintype.card_congr F.ord, ← Fintype.card_congr F'.ord]
  rw [← map_inv F.conj, coords_mul]
end GlobalTheory.StepData.LatFrame
