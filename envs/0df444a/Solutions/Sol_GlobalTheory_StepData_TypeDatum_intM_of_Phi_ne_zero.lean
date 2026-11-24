-- Prove2me | solution 1 for GlobalTheory.StepData.TypeDatum.intM_of_Phi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:53:33.216926+00:00
-- url     : https://prove2.me/submissions/63608641-71f0-42bb-8a30-bda729a68bed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_MaxM_intM
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
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
open GlobalTheory.StepData.TypeDatum
variable (P : TypeDatum k a)
omit [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData.TypeDatum
theorem _root_.solution (μ : kˣ →* ℂˣ) {x : Matrix (a ⊕ t) a k} (h : P.Phi t μ x ≠ 0) : IntM x := by
  obtain ⟨⟨g, hg, e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 h
  rintro (i | i) j
  · have := intM_of_mem_KO (P.le_KO hg) i j
    rwa [e] at this
  · exact h2.intM i j
end GlobalTheory.StepData.TypeDatum
