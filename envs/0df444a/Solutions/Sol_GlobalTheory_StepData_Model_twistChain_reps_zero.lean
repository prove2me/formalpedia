-- Prove2me | solution 1 for GlobalTheory.StepData.Model.twistChain_reps_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:11:32.131794+00:00
-- url     : https://prove2.me/submissions/9bbe1b28-b702-46bf-a6f0-8262833e4623

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Theorems.Thm_GlobalTheory_StepData_mem_latOf_one
import Theorems.Thm_GlobalTheory_StepData_normalBasis_val


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
open GlobalTheory GlobalTheory.StepData GlobalTheory.StepData.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {κ t : Type*} [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData.Model
theorem _root_.solution [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ)
    (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (ν' : ℕ → kˣ →* ℂˣ) :
    let T := twistChain 0 t κ δ hδ ν'
    let A : RepFam k 0 (XIx κ t) := fun _ _ _ => {1}
    T.IsRepSystem A ψ ν ∧ T.RepsInStab A ∧ T.RepsMeet A ∧ T.RepsNormal A ϖ ∧ T.RepsOne A := by
  refine ⟨⟨fun _ _ => rfl, fun j c h => by omega⟩, ?_, ?_, ?_, fun _ _ _ _ hg _ => hg⟩
  · rintro j c h _ rfl; exact one_mem _
  · rintro j c h _ rfl y
    change _ ∈ latOf (1 * 1) ↔ _
    simp [mem_latOf_one]
  · rintro j c h _ rfl
    refine ⟨0, 0, by simp, by simp, ?_⟩
    change latOf (1 * 1) = _
    congr 1
    refine Units.ext ?_
    rw [normalBasis_val, mul_one, Units.val_one, ← fromBlocks_one]
    congr 1
    · ext; simp
    · simp
end GlobalTheory.StepData.Model
