-- Prove2me | solution 1 for GlobalTheory.LastSteps.latInd_eq_finsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:36:23.778002+00:00
-- url     : https://prove2.me/submissions/04030d5e-04af-405b-8a40-f6d7d521250f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_exists_pull
import Theorems.Thm_GlobalTheory_LastSteps_compInd_of_not

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
namespace GlobalTheory.LastSteps
theorem _root_.solution (fW : Module.Dual 𝓀[k] (Red LY)) :
    latInd L LY x₀ = ∑ᶠ f' : Module.Dual 𝓀[k] (Red L), compInd L LY f' fW x₀ := by
  by_cases h : ∀ z ∈ L, x₀ *ᵥ z ∈ LY
  · obtain ⟨f₀, -, hf⟩ := exists_pull h fW
    simpa [latInd, if_pos h] using (hf fun _ => 1).symm
  · simp [compInd_of_not h, latInd, if_neg h]
end GlobalTheory.LastSteps
