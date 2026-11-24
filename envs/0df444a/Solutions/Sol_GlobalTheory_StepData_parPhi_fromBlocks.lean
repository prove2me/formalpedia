-- Prove2me | solution 1 for GlobalTheory.StepData.parPhi_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:14.048993+00:00
-- url     : https://prove2.me/submissions/737d4973-f0f3-424d-a6ab-f3bf4e214e18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_parPhi_of_mem

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
variable {r s s' : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
omit [Fintype s] [DecidableEq s] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.StepData
theorem _root_.solution (δ : kˣ →* ℂˣ) {A : Matrix r r k} {B : Matrix r s' k} {C : Matrix s r k} {D : Matrix s s' k}
    {g : GL r k} (hg : g ∈ KO k r) (e : g.val = A) (h21 : MaxM C) (h12 : IntM B) (h22 : IntM D) :
    parPhi δ (fromBlocks A B C D) = ((δ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) :=
  parPhi_of_mem δ hg e h21 h12 h22
end GlobalTheory.StepData
