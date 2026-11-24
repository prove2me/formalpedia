-- Prove2me | solution 1 for GlobalTheory.LastSteps.integrable_qLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:36:28.032405+00:00
-- url     : https://prove2.me/submissions/19b14f65-1f05-4a6d-9941-25eddfa8548f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_isClopen_isCompact_qLat
import Theorems.Thm_GlobalTheory_LatPair_ite_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


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
variable [Fintype n]
variable [MeasurableSpace k] [BorelSpace k] (q : Unif k) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
  (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
include hψ
open Classical
namespace GlobalTheory.LastSteps
theorem _root_.solution (η : n → k) :
    Integrable (fun y => (if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ y) : ℂ)) μ := by
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨h1, h2⟩ := isClopen_isCompact_qLat q L
  have h3 := ite_mem_SB h1 h2
  refine Continuous.integrable_of_hasCompactSupport (h3.1.continuous.mul ?_) h3.2.mul_right
  exact continuous_subtype_val.comp (hψ.continuous.comp (continuous_const.dotProduct continuous_id))
end GlobalTheory.LastSteps
