-- Prove2me | solution 1 for GlobalTheory.StepData.TypeDatum.Phi_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:04:19.4058+00:00
-- url     : https://prove2.me/submissions/2cecb086-61cd-441f-b915-d84e62021e82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_extZ_add
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_MaxM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg


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
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
open GlobalTheory.StepData.TypeDatum
variable (P : TypeDatum k a)
open Classical
omit [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData.TypeDatum
theorem _root_.solution {μ : kˣ →* ℂˣ} (hμ : IsTame μ) (x : Matrix (a ⊕ t) a k) {y : Matrix (a ⊕ t) a k} (hy : MaxM y) :
    P.Phi t μ (x + y) = P.Phi t μ x := by
  have h2 : MaxM y.toRows₂ := fun i j => hy _ _
  have e : MaxM (x + y).toRows₂ ↔ MaxM x.toRows₂ :=
    ⟨fun h => by simpa using (show MaxM (x.toRows₂ + y.toRows₂) from h).add h2.neg, fun h => h.add h2⟩
  have e' : extZ P.J (P.rho μ) (x + y).toRows₁ = extZ P.J (P.rho μ) x.toRows₁ :=
    P.extZ_add hμ x.toRows₁ (Y := y.toRows₁) fun i j => hy _ _
  unfold Phi
  exact if_congr e e' rfl
end GlobalTheory.StepData.TypeDatum
