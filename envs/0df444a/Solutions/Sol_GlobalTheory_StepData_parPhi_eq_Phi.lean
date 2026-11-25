-- Prove2me | solution 1 for GlobalTheory.StepData.parPhi_eq_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:22:43.584332+00:00
-- url     : https://prove2.me/submissions/4ec989d5-4ceb-4b2d-a369-8a7e6e47d3e3

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
omit [Fintype s] [DecidableEq s]
namespace GlobalTheory.StepData
theorem _root_.solution [IsEmpty s'] (δ : kˣ →* ℂˣ)
    (x : Matrix (r ⊕ s) (r ⊕ s') k) : parPhi δ x = (TypeDatum.full k r).Phi s δ x.toCols₁ := by
  have e4 : (δ.comp (Matrix.GeneralLinearGroup.det.comp (KO k r).subtype))⁻¹ = (TypeDatum.full k r).rho δ :=
    (one_mul _).symm
  by_cases h : MaxM x.toBlocks₂₁
  · rw [parPhi, if_pos ⟨h, fun _ j => isEmptyElim j, fun _ j => isEmptyElim j⟩, TypeDatum.Phi,
      if_pos (show MaxM x.toCols₁.toRows₂ from h), e4]; rfl
  · rw [parPhi, if_neg fun H => h H.1, TypeDatum.Phi, if_neg (show ¬ MaxM x.toCols₁.toRows₂ from h)]
end GlobalTheory.StepData
