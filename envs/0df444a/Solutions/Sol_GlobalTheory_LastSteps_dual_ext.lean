-- Prove2me | solution 1 for GlobalTheory.LastSteps.dual_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:42.181874+00:00
-- url     : https://prove2.me/submissions/a89ecdfc-ec3d-4dea-a97d-1adf9692bca9

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
namespace GlobalTheory.LastSteps
theorem _root_.solution {L : Submodule 𝒪[k] (n → k)} {f g : Module.Dual 𝓀[k] (Red L)}
    (h : ∀ z, f (Red.mk L z) = g (Red.mk L z)) : f = g :=
  LinearMap.ext fun x => by
    obtain ⟨z, rfl⟩ := Red.mk_surjective L x
    exact h z
end GlobalTheory.LastSteps
