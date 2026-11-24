-- Prove2me | solution 1 for GlobalTheory.StepData.Chain.ofType_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:27:04.854213+00:00
-- url     : https://prove2.me/submissions/fc60d687-5f68-47b4-bacc-af5e4c5ab69e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_iterPhi_mem_SB
import Theorems.Thm_GlobalTheory_StepData_LatFrame_transport_mem_SB
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_map_conj

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
variable {s : ℕ} {X : ℕ → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type*} [Fintype Z] [DecidableEq Z]
variable {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData
namespace Chain
theorem _root_.solution (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z) :
    (Chain.ofType P μ hμ F Ftop).Regular :=
  ⟨fun _ _ _ => LatFrame.transport_mem_SB _ _ (P.iterPhi_mem_SB μ hμ _),
    LatFrame.transport_mem_SB _ _ (P.iterPhi_mem_SB μ hμ _), fun _ _ _ => TypeDatum.map_conj _ _⟩
end Chain
end GlobalTheory.StepData
