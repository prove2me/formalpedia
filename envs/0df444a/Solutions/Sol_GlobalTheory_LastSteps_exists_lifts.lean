-- Prove2me | solution 1 for GlobalTheory.LastSteps.exists_lifts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:36:26.550831+00:00
-- url     : https://prove2.me/submissions/b9be13fc-dd11-4f5b-9f3b-5812e3a97ae8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_exists_dual

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
variable [Fintype n] {L : Submodule 𝒪[k] (n → k)} {F : n → k}
namespace GlobalTheory.LastSteps
theorem _root_.solution (h : InDual L F) : ∃ f, Lifts L F f := by
  let G : L →ₗ[𝒪[k]] 𝒪[k] :=
    { toFun := fun y => ⟨F ⬝ᵥ y, h y y.2⟩
      map_add' := fun y z => Subtype.ext (by simp [dotProduct_add])
      map_smul' := fun s y => Subtype.ext (dotProduct_smul s F (y : n → k)) }
  obtain ⟨f, hf⟩ := exists_dual L (Algebra.linearMap 𝒪[k] 𝓀[k] ∘ₗ G)
  exact ⟨f, fun y => ⟨G y, rfl, (hf y).symm⟩⟩
end GlobalTheory.LastSteps
