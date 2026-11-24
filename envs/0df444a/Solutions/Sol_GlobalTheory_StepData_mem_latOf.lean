-- Prove2me | solution 1 for GlobalTheory.StepData.mem_latOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:51:48.254849+00:00
-- url     : https://prove2.me/submissions/fd3b4c4e-ef6e-4c5e-a3a4-4a51cc6f9849

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
variable {k : Type*} [Field k]
variable {ι ι' Y Y' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
variable [ValuativeRel k]
namespace GlobalTheory.StepData
theorem _root_.solution {g : GL Y k} {y : Y → k} : y ∈ latOf g ↔ ∀ i, ((g⁻¹).val *ᵥ y) i ∈ 𝒪[k] := Iff.rfl
end GlobalTheory.StepData
