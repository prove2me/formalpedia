-- Prove2me | solution 1 for GlobalTheory.LastSteps.term_eq_finsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:51.552804+00:00
-- url     : https://prove2.me/submissions/7a7c4ed3-a925-4ad3-9c92-9002b6a61935

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
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (P : Pair k n')
namespace GlobalTheory.LastSteps
theorem _root_.solution (fW : Module.Dual 𝓀[k] (Red LY)) :
    term q χ ε P LY fW x₀ = ∑ᶠ f' : Module.Dual 𝓀[k] (Red P.ker),
      χ (-((ε : 𝓀[k]) * f' (qvec q P))) * compInd P.ker LY f' fW x₀ := by
  by_cases h : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ LY
  · obtain ⟨f₀, h0, hf⟩ := exists_pull h fW
    rw [hf fun f' => χ (-((ε : 𝓀[k]) * f' (qvec q P))), term, dif_pos h, qvec, h0]
  · simp [compInd_of_not h, term, dif_neg h]
end GlobalTheory.LastSteps
