-- Prove2me | solution 1 for GlobalTheory.PairOp.cntIp_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:49.413727+00:00
-- url     : https://prove2.me/submissions/0a78741b-d9ba-4e6e-b20a-e9bbd975c7e9

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
section
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
namespace GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
section Adjoint
variable {A B A' B' : Module.End ℂ (Form k n ℂ)}
private theorem finsum_const_mul_eq_mul_finsum {ι : Type} (a : ℂ) (f : ι → ℂ) : ∑ᶠ i, a * f i = a * ∑ᶠ i, f i := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hf : (Function.support f).Finite
  · exact (mul_finsum f a).symm
  · rw [finsum_of_infinite_support hf, mul_zero]
    exact finsum_of_infinite_support fun h => hf (h.subset fun i hi => mul_ne_zero ha hi)
end Adjoint
end GlobalTheory.PairOp
end
end

set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
variable {A B A' B' : Module.End ℂ (Form k n ℂ)}
namespace GlobalTheory.PairOp
theorem _root_.solution (a : ℂ) (φ φ' : Form k n ℂ) : cntIp φ (a • φ') = (starRingEnd ℂ) a * cntIp φ φ' := by
  unfold cntIp
  rw [← finsum_const_mul_eq_mul_finsum]
  exact finsum_congr fun P => by simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
end GlobalTheory.PairOp
