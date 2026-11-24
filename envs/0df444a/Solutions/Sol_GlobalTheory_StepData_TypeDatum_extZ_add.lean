-- Prove2me | solution 1 for GlobalTheory.StepData.TypeDatum.extZ_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:53:18.615363+00:00
-- url     : https://prove2.me/submissions/9ef4d81c-1bdb-48a8-8ab2-8bb2efa7f040

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
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
namespace GlobalTheory.StepData.TypeDatum
theorem _root_.solution {μ : kˣ →* ℂˣ} (hμ : IsTame μ) (M : Matrix a a k) {Y : Matrix a a k} (hY : MaxM Y) :
    extZ P.J (P.rho μ) (M + Y) = extZ P.J (P.rho μ) M := by
  by_cases h : ∃ g ∈ P.J, g.val = M
  · obtain ⟨g, hg, rfl⟩ := h
    obtain ⟨g', hg', e⟩ := P.exists_of_congr hg (M := g.val + Y) (by simpa using hY)
    rw [← e, extZ_coe _ _ ⟨g', hg'⟩, extZ_coe _ _ ⟨g, hg⟩, P.rho_congr hμ (g := ⟨g, hg⟩) (by simpa [e] using hY)]
  · rw [extZ_of_not _ _ h, extZ_of_not]
    rintro ⟨g, hg, e⟩
    exact h (P.exists_of_congr hg (by simpa [e] using hY.neg))
end GlobalTheory.StepData.TypeDatum
