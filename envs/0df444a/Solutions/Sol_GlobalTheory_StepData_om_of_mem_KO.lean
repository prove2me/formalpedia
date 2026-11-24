-- Prove2me | solution 1 for GlobalTheory.StepData.om_of_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:54:37.679971+00:00
-- url     : https://prove2.me/submissions/396d934d-64e6-462e-8b77-487dadaa7877

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_StepData_valuation_det_of_mem_KO


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
namespace GlobalTheory.StepData
theorem _root_.solution (μ : kˣ →* ℂˣ) {g : GL a k} (hg : g ∈ KO k a) {h : GL b k}
    (hh : h ∈ KO k b) (Φ : Matrix b a k → ℂ) (x : Matrix b a k) :
    om μ g h Φ x = (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) *
      Φ ((h⁻¹).val * x * g.val) := by
  simp [om, nabs_eq_one_of_valuation_eq_one (valuation_det_of_mem_KO hg),
    nabs_eq_one_of_valuation_eq_one (valuation_det_of_mem_KO hh)]
end GlobalTheory.StepData
