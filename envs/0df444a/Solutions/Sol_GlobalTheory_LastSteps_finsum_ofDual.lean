-- Prove2me | solution 1 for GlobalTheory.LastSteps.finsum_ofDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:47.69206+00:00
-- url     : https://prove2.me/submissions/b10df615-4ebd-41b4-b425-dbdf22bcf433

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
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
theorem _root_.solution {A : Type} [AddCommMonoid A] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (F : Pair k n → A) :
    ∑ᶠ f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}, F (ofDual L f) = ∑ P ∈ withLat L, F P := by
  letI := Fintype.ofFinite {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}
  rw [finsum_eq_sum_of_fintype, sum_withLat]
end GlobalTheory.LastSteps
