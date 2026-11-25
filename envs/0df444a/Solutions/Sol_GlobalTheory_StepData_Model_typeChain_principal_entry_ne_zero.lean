-- Prove2me | solution 1 for GlobalTheory.StepData.Model.typeChain_principal_entry_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:11:42.891794+00:00
-- url     : https://prove2.me/submissions/50ca3a2a-1ff1-41fa-9b53-dff04d138b8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Theorems.Thm_GlobalTheory_StepData_Model_typeChain_entry_ne_zero
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_eq_one
import Theorems.Thm_GlobalTheory_StepData_mem_KOne
import Theorems.Thm_GlobalTheory_StepData_tame_det_of_mem_KOne


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
variable [MeasurableSpace k] [BorelSpace k] {κ t : Type*} [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData.Model
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] {ϖ : kˣ} (hϖ : ∀ z : k, valuation k z < 1 → valuation k z ≤ valuation k (ϖ : k)) (s c : ℕ)
    (h : 0 + 1 + c = s) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) :
    (typeChain t ϖ (TypeDatum.principal k (κ ⊕ Fin (s + 1))) μ hμ).entry ψ ν 0 c h 1 1 ≠ 0 := by
  refine (typeChain_entry_ne_zero ψ ν ϖ s c h _ μ hμ fun g => ?_).2
  have hi : ∑ i : Fin s, (g : GL (κ ⊕ Fin (s + 1)) k).val (.inr i.castSucc) (.inr i.succ) / ϖ ∈ 𝒪[k] := sum_mem fun i _ => by
    have := hϖ _ (mem_KOne.1 g.2 (.inr i.castSucc) (.inr i.succ))
    rw [Matrix.sub_apply, Matrix.one_apply_ne (by simp [Fin.ext_iff]), sub_zero] at this
    rw [Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ this zero_le
  rw [hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi), TypeDatum.rho_apply, tame_det_of_mem_KOne (hμ 1) g.2]
  change ((1 * 1⁻¹ : ℂˣ) : ℂ) = _
  simp
end GlobalTheory.StepData.Model
