-- Prove2me | solution 1 for GlobalTheory.LastSteps.finsum_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:48.449796+00:00
-- url     : https://prove2.me/submissions/8f696653-b742-4284-8b87-b74eca906890

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
theorem _root_.solution {V A : Type} [Finite V] [Zero V] [AddCommMonoid A] (F : V → A) :
    ∑ᶠ v, F v = F 0 + ∑ᶠ v : {v : V // v ≠ 0}, F v := by
  classical
  letI := Fintype.ofFinite V
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Fintype.sum_eq_add_sum_subtype_ne F 0]
end GlobalTheory.LastSteps
