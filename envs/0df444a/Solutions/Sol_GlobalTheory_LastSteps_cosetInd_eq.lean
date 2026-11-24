-- Prove2me | solution 1 for GlobalTheory.LastSteps.cosetInd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:46.446426+00:00
-- url     : https://prove2.me/submissions/663b6091-6269-4f30-aef0-5fe5838f9deb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat

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
open Classical
namespace GlobalTheory.LastSteps
theorem _root_.solution (q : Unif k) (f : Module.Dual 𝓀[k] (Red L)) (η : n → k) :
    cosetInd q L f η = if Lifts L (q.1 • η) f then 1 else 0 := by
  refine if_congr ⟨fun ⟨F, hF, hD⟩ y => ?_, fun h => ⟨_, h, fun y _ => by simp⟩⟩ rfl rfl
  obtain ⟨s, hs, e⟩ := hF y
  refine ⟨s + q.1 * ⟨_, hD y y.2⟩, ?_, ?_⟩
  · have : q.1 • η = F + q.1 • (η - q.inv • F) := by rw [smul_sub, q.smul_inv_smul]; abel
    rw [this, add_dotProduct, smul_dotProduct, ← hs]
    rfl
  · rw [map_add, map_mul, (residue_eq_zero_iff _).2 q.mem_max, zero_mul, add_zero, e]
end GlobalTheory.LastSteps
