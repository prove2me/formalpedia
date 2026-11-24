-- Prove2me | solution 1 for GlobalTheory.StepData.TypeDatum.Phi_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:19.376071+00:00
-- url     : https://prove2.me/submissions/ca52d042-6957-49ab-95c4-216c97403109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_eq_mul_of_support
import Theorems.Thm_GlobalTheory_StepData_MaxM_mul_intM
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
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open GlobalTheory.StepData.TypeDatum
variable (P : TypeDatum k a) {μ : kˣ →* ℂˣ}
omit [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData.TypeDatum
theorem _root_.solution (g : P.J) (x : Matrix (a ⊕ t) a k) :
    P.Phi t μ (x * (g : GL a k).val) = P.rho μ g * P.Phi t μ x := by
  refine eq_mul_of_support (G := P.J) (fun g x => x * (g : GL a k).val) (fun g x => by simp [Matrix.mul_assoc])
    (c := P.rho μ) (fun g x hx => ?_) g x
  obtain ⟨⟨g', hg', e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 hx
  rw [P.Phi_of_mem μ ⟨g', hg'⟩ e h2, P.Phi_of_mem μ (⟨g', hg'⟩ * g) (by rw [Subgroup.coe_mul, Units.val_mul, e]; rfl)
    (h2.mul_intM (intM_of_mem_KO (P.le_KO g.2))), ← Units.val_mul, ← Units.val_mul, ← rho_apply, ← rho_apply,
    map_mul, Units.val_mul, mul_comm]
end GlobalTheory.StepData.TypeDatum
