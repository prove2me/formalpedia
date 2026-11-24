-- Prove2me | solution 1 for GlobalTheory.LastSteps.phiOne_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:50:10.207706+00:00
-- url     : https://prove2.me/submissions/2435c236-3d26-4d12-abe6-8bc9d086c5e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_lastPair_hasVal

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
variable [Fintype n']
omit [Fintype n']
open Classical
namespace GlobalTheory.LastSteps
theorem _root_.solution [Fintype n] (q : Unif k) (LY : Submodule 𝒪[k] (n → k)) [LY.IsLattice k]
    (L : Submodule 𝒪[k] (n'' → k)) [L.IsLattice k] (fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0})
    (x' : Matrix n'' n k) (η : n → k) :
    phiOne (ofDual LY fW) (lastPair q L) (withRow x' η) =
      latInd LY L x' * (if Lifts LY (q.1 • η) fW.1 then 1 else 0) := by
  have h1 : ∀ y, (withRow x' η *ᵥ y) ∘ Sum.inl = x' *ᵥ y := fun y => rfl
  have h2 : ∀ y, q.1 • (withRow x' η *ᵥ y) (Sum.inr 0) = (q.1 • η) ⬝ᵥ y := fun y => by
    rw [smul_dotProduct]; rfl
  rw [latInd, ite_zero_mul_ite_zero, mul_one]
  refine if_congr ?_ rfl rfl
  simp only [maps_iff_hasVal, lastPair_hasVal, h1, h2]
  exact ⟨fun h => ⟨fun y hy => (h y _ (ofDual_hasVal LY fW ⟨y, hy⟩)).1, fun y => (h y _ (ofDual_hasVal LY fW y)).2⟩,
    fun h y a ⟨hy, ha⟩ => ⟨h.1 y hy, ha ▸ h.2 ⟨y, hy⟩⟩⟩
end GlobalTheory.LastSteps
