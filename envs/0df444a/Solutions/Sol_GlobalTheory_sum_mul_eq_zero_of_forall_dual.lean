-- Prove2me | solution 1 for GlobalTheory.sum_mul_eq_zero_of_forall_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:07.789477+00:00
-- url     : https://prove2.me/submissions/d1f0e27e-6a34-4403-b3da-cddc76dfff74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureCones

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F K σ : Type} [Field F] [Field K] [Algebra F K]
    (S : Finset σ) (c m : σ → K)
    (h : ∀ l : K →ₗ[F] F, ∑ s ∈ S, l (c s) • m s = 0) : ∑ s ∈ S, c s * m s = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F K
  let T := S.biUnion fun s => (b.repr (c s)).support
  have hc : ∀ s ∈ S, c s = ∑ j ∈ T, b.coord j (c s) • b j := fun s hs => by
    conv_lhs => rw [← b.linearCombination_repr (c s)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset (s := T)]
    · rfl
    · exact Finset.subset_biUnion_of_mem (fun s => (b.repr (c s)).support) hs
    · simp
  calc ∑ s ∈ S, c s * m s = ∑ s ∈ S, ∑ j ∈ T, b j * (b.coord j (c s) • m s) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        conv_lhs => rw [hc s hs]
        rw [Finset.sum_mul]
        simp
    _ = 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← Finset.mul_sum, h, mul_zero]
end GlobalTheory
