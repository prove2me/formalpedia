-- Prove2me | solution 1 for GlobalTheory.LastSteps.exists_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:40.293797+00:00
-- url     : https://prove2.me/submissions/6a668eca-9b7c-456c-aa9d-d92aab416e72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_exists_dual
import Theorems.Thm_GlobalTheory_LastSteps_dual_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
open GlobalTheory GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
variable [Fintype n'] {L : Submodule 𝒪[k] (n' → k)} {LY : Submodule 𝒪[k] (n → k)} {x₀ : Matrix n n' k}
open Classical
namespace GlobalTheory.LastSteps
theorem _root_.solution (h : ∀ z ∈ L, x₀ *ᵥ z ∈ LY) (fW : Module.Dual 𝓀[k] (Red LY)) :
    ∃ f₀ : Module.Dual 𝓀[k] (Red L), (∀ z : L, f₀ (Red.mk L z) = fW (Red.mk LY ⟨x₀ *ᵥ z, h z z.2⟩)) ∧
      ∀ w : Module.Dual 𝓀[k] (Red L) → ℂ, ∑ᶠ f', w f' * compInd L LY f' fW x₀ = w f₀ := by
  obtain ⟨f₀, hf⟩ := exists_dual L (fW.restrictScalars 𝒪[k] ∘ₗ Red.mk LY ∘ₗ
    ((mulVecLin x₀).restrictScalars 𝒪[k]).restrict h)
  have hf' : ∀ z : L, f₀ (Red.mk L z) = fW (Red.mk LY ⟨x₀ *ᵥ z, h z z.2⟩) := hf
  refine ⟨f₀, hf', fun w => ?_⟩
  rw [finsum_eq_single _ f₀ fun f' hne => ?_, compInd, if_pos ⟨h, fun z => (hf' z).symm⟩, mul_one]
  rw [compInd, if_neg, mul_zero]
  rintro ⟨_, h'⟩
  exact hne (dual_ext fun z => (h' z).symm.trans (hf' z).symm)
end GlobalTheory.LastSteps
