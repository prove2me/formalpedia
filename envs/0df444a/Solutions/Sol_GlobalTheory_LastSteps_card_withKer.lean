-- Prove2me | solution 1 for GlobalTheory.LastSteps.card_withKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:36:25.140686+00:00
-- url     : https://prove2.me/submissions/c1bbb7af-3a70-4919-8804-a52a8281ecb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LatPair_sum_withKer
import Theorems.Thm_GlobalTheory_LatPair_sum_withLat


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
namespace GlobalTheory.LastSteps
theorem _root_.solution (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : (withKer L).card = (withLat L).card := by
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  letI := Fintype.ofFinite {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}
  letI := Fintype.ofFinite {x : Red L // x ≠ 0}
  let e : Red L ≃ₗ[𝓀[k]] Module.Dual 𝓀[k] (Red L) := LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq.symm
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, sum_withKer L q, sum_withLat]
  exact Fintype.sum_equiv (e.toEquiv.subtypeEquiv fun x => by simp) _ _ fun _ => rfl
end GlobalTheory.LastSteps
