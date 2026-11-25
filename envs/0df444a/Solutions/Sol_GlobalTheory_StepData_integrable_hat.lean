-- Prove2me | solution 1 for GlobalTheory.StepData.integrable_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:09.55997+00:00
-- url     : https://prove2.me/submissions/ed80b1bb-44d9-4090-8e62-6ce83ec82867

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_IntM_mul


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
variable {k : Type*} [Field k] {n n' : Type*}
variable [ValuativeRel k]
variable [Fintype n] [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (ε : k)
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k]
namespace GlobalTheory.StepData
theorem _root_.solution [ν.IsAddHaarMeasure] (hψ : Continuous ψ) {f : (n → k) → ℂ} (hf : f ∈ SB (n → k))
    (η : n → k) : Integrable (fun y => f y * (ψ (ε * (η ⬝ᵥ y)) : ℂ)) (Measure.pi fun _ => ν) := by
  have := secondCountable k
  have := t2Space k
  refine Continuous.integrable_of_hasCompactSupport (hf.1.continuous.mul ?_) hf.2.mul_right
  exact continuous_subtype_val.comp (hψ.comp (by fun_prop))
end GlobalTheory.StepData
