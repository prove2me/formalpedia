-- Prove2me | solution 1 for GlobalTheory.StepData.TypeDatum.Phi_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:14:37.414437+00:00
-- url     : https://prove2.me/submissions/68ddb7c8-4b35-450f-aa7f-39f9d47b794e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_Phi_add
import Theorems.Thm_GlobalTheory_StepData_eq_mul_of_support
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_IntM_mul_maxM
import Theorems.Thm_GlobalTheory_StepData_MaxM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_mul_intM
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_maxM_zero


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
open GlobalTheory.StepData.TypeDatum
variable (P : TypeDatum k a) {μ : kˣ →* ℂˣ}
namespace GlobalTheory.StepData.TypeDatum
theorem _root_.solution (hμ : IsTame μ) (h : P.stepJ t) (x : Matrix (a ⊕ t) a k) :
    P.Phi t μ ((h : GL (a ⊕ t) k).val * x) = P.rho μ (P.corner h) * P.Phi t μ x := by
  refine eq_mul_of_support (G := P.stepJ t) (fun g x => (g : GL (a ⊕ t) k).val * x)
    (fun g x => by simp [← Matrix.mul_assoc]) (c := fun h => P.rho μ (P.corner h)) (fun h x hx => ?_) h x
  obtain ⟨⟨g', hg', e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 hx
  obtain ⟨-, -, hB, hC, D, hD, eD⟩ := h.2
  have e0 : (h : GL (a ⊕ t) k).val * x = fromRows ((P.corner h : GL a k).val * g'.val) 0 +
      fromRows ((h : GL (a ⊕ t) k).val.toBlocks₁₂ * x.toRows₂)
        ((h : GL (a ⊕ t) k).val.toBlocks₂₁ * g'.val + D.val * x.toRows₂) := by
    conv_lhs => rw [← fromBlocks_toBlocks (h : GL (a ⊕ t) k).val, ← fromRows_toRows x, fromBlocks_mul_fromRows]
    rw [corner_val, e, eD]
    ext (i | i) j <;> simp
  rw [e0, P.Phi_add hμ, P.Phi_of_mem μ ⟨g', hg'⟩ e h2, P.Phi_of_mem μ (P.corner h * ⟨g', hg'⟩) (by simp)
    (by simpa using maxM_zero), ← Units.val_mul, ← Units.val_mul, ← rho_apply, ← rho_apply, map_mul, Units.val_mul]
  rintro (i | i) j
  · exact hB.mul_maxM h2 i j
  · exact (hC.mul_intM (intM_of_mem_KO (P.le_KO hg'))).add ((intM_of_mem_KO hD).mul_maxM h2) i j
end GlobalTheory.StepData.TypeDatum
