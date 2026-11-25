-- Prove2me | solution 1 for GlobalTheory.StepData.Model.isColChar_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:11:26.213896+00:00
-- url     : https://prove2.me/submissions/144462db-2dd7-424b-991e-e7952ffdfa26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_eq_one
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO


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
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.StepData.Model
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) :
    IsColChar ψ (TypeDatum.full k (n ⊕ Fin c)).toLevel 1 1 := by
  intro g u _ hm
  have hK : IntM (u * embX c (g : GL n k)).val := by
    have : u * embX c (g : GL n k) ∈ (TypeDatum.full k (n ⊕ Fin c)).J := by simpa using hm
    exact intM_of_mem_KO this
  have hs : simpleSum u ∈ 𝒪[k] := by
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    split_ifs
    · have := hK (.inr i) (.inr j)
      rw [Units.val_mul, ← fromBlocks_toBlocks u.val] at this
      change (_ * fromBlocks _ 0 0 1 : Matrix _ _ k) _ _ ∈ _ at this
      simpa [fromBlocks_multiply, toBlocks₂₂] using this
    · exact zero_mem _
  rw [hψ.eq_one (show _ ∈ cball (1 : kˣ) from hs)]
  change _ = _ * (((1 : ℂˣ)⁻¹ : ℂˣ) : ℂ)
  simp
end GlobalTheory.StepData.Model
