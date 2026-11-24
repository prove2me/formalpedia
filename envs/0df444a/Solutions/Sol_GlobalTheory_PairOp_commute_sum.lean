-- Prove2me | solution 1 for GlobalTheory.PairOp.commute_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:38.080294+00:00
-- url     : https://prove2.me/submissions/583479c0-4774-4d8f-aaeb-1e9c35fa2f8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
namespace GlobalTheory.PairOp
theorem _root_.solution {A : Module.End ℂ (Form k n M)} (h : ∀ c : 𝓀[k]ˣ, A * dia c = dia c * A) {ι : Type}
    (s : Finset ι) (a : ι → ℂ) (e : ι → 𝓀[k]ˣ) :
    A * (∑ i ∈ s, a i • dia (e i)) = (∑ i ∈ s, a i • dia (e i)) * A := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, h]
end GlobalTheory.PairOp
