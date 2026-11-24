-- Prove2me | solution 1 for GlobalTheory.StepData.parPhi_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:20.188652+00:00
-- url     : https://prove2.me/submissions/a8341725-d5ff-434d-8526-ceaf1b372d25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_extZ_add
import Theorems.Thm_GlobalTheory_StepData_mem_SB_of_periodic
import Theorems.Thm_GlobalTheory_StepData_parPhi_ne_zero_iff
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_MaxM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_intM
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg
import Theorems.Thm_GlobalTheory_StepData_intM_fromBlocks
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_maxM_fromBlocks


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
open Classical
omit [DecidableEq s]
namespace GlobalTheory.StepData
theorem _root_.solution [Fintype s'] {δ : kˣ →* ℂˣ} (hδ : IsTame δ) :
    parPhi δ ∈ SB (Matrix (r ⊕ s) (r ⊕ s') k) := by
  refine mem_SB_of_periodic (fun x hx => ?_) fun x y hy => ?_
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 hx
    rw [← fromBlocks_toBlocks x, ← e]
    exact intM_fromBlocks.2 ⟨intM_of_mem_KO hg, h12, h21.intM, h22⟩
  · rw [← fromBlocks_toBlocks y] at hy
    obtain ⟨y11, y12, y21, y22⟩ := maxM_fromBlocks.1 hy
    have e1 : MaxM (x + y).toBlocks₂₁ ↔ MaxM x.toBlocks₂₁ :=
      ⟨fun h => by simpa using (show MaxM (x.toBlocks₂₁ + y.toBlocks₂₁) from h).add y21.neg, fun h => h.add y21⟩
    have e2 : IntM (x + y).toBlocks₁₂ ↔ IntM x.toBlocks₁₂ :=
      ⟨fun h => by simpa using (show IntM (x.toBlocks₁₂ + y.toBlocks₁₂) from h).add y12.intM.neg,
        fun h => h.add y12.intM⟩
    have e3 : IntM (x + y).toBlocks₂₂ ↔ IntM x.toBlocks₂₂ :=
      ⟨fun h => by simpa using (show IntM (x.toBlocks₂₂ + y.toBlocks₂₂) from h).add y22.intM.neg,
        fun h => h.add y22.intM⟩
    unfold parPhi
    have e4 : (δ.comp (Matrix.GeneralLinearGroup.det.comp (KO k r).subtype))⁻¹ = (TypeDatum.full k r).rho δ :=
      (one_mul _).symm
    rw [e4]
    exact if_congr (and_congr e1 (and_congr e2 e3)) ((TypeDatum.full k r).extZ_add hδ x.toBlocks₁₁ y11) rfl
end GlobalTheory.StepData
