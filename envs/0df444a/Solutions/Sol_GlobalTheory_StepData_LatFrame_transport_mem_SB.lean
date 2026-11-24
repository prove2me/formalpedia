-- Prove2me | solution 1 for GlobalTheory.StepData.LatFrame.transport_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:53:31.381032+00:00
-- url     : https://prove2.me/submissions/8ac92480-a7c0-48bc-8113-f4fb59454a3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous


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
omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
namespace GlobalTheory.StepData.LatFrame
theorem _root_.solution (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') {Φ : Matrix ι ι' k → ℂ}
    (hΦ : Φ ∈ SB (Matrix ι ι' k)) : F.transport F' Φ ∈ SB (Matrix Y Y' k) := by
  let e : Matrix Y Y' k ≃ₜ Matrix ι ι' k :=
    { Matrix.reindex F.ord.symm F'.ord.symm with
      continuous_toFun := continuous_id.matrix_reindex _ _
      continuous_invFun := continuous_id.matrix_reindex _ _ }
  let e' := (sideMul F'.bas F.bas).trans e
  exact ⟨hΦ.1.comp_continuous e'.continuous, hΦ.2.comp_homeomorph e'⟩
end GlobalTheory.StepData.LatFrame
