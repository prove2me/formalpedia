-- Prove2me | solution 1 for GlobalTheory.StepData.parPhi_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:53:34.620886+00:00
-- url     : https://prove2.me/submissions/85f4508e-b660-4bef-bec5-58239bfd2d6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock

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
theorem _root_.solution (δ : kˣ →* ℂˣ) {x : Matrix (r ⊕ s) (r ⊕ s') k} {g : GL r k} (hg : g ∈ KO k r)
    (e : g.val = x.toBlocks₁₁) (h21 : MaxM x.toBlocks₂₁) (h12 : IntM x.toBlocks₁₂) (h22 : IntM x.toBlocks₂₂) :
    parPhi δ x = ((δ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) := by
  rw [parPhi, if_pos ⟨h21, h12, h22⟩, ← e, extZ_coe _ _ ⟨g, hg⟩]; rfl
end GlobalTheory.StepData
