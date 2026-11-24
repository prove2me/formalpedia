-- Prove2me | solution 1 for GlobalTheory.PairOp.mem_ram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:52.164761+00:00
-- url     : https://prove2.me/submissions/ab16f2eb-a113-4768-a385-e32f2a6d1c22

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
theorem _root_.solution {A : Module.End ℂ (Form k n M)} (h : ∀ c : 𝓀[k]ˣ, A * dia c = dia c * A) {φ : Form k n M}
    (hφ : φ ∈ Mram k n M) : A φ ∈ Mram k n M := by
  simp only [Mram, LinearMap.mem_ker] at hφ ⊢
  have hc : (Nm : Module.End ℂ (Form k n M)) * A = A * Nm := by
    unfold Nm
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => (h c).symm
  rw [← Module.End.mul_apply, hc, Module.End.mul_apply, hφ, map_zero]
end GlobalTheory.PairOp
