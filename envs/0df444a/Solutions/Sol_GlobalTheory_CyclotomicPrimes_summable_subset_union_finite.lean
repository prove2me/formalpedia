-- Prove2me | solution 1 for GlobalTheory.CyclotomicPrimes.summable_subset_union_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:08:20.325146+00:00
-- url     : https://prove2.me/submissions/834ae619-ed5e-4a1f-a1ca-a71f302bb6eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SummableInvAbsNormPrimesOfNotPrimeNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsContinuousNormCharLFunctionNeZeroOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeNormCyclotomicCharNeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DedekindZetaEulerProductMulSubOneEntireNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeAbsNormEqOfIrreducibleCyclotomic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.CyclotomicPrimes
namespace GlobalTheory.CyclotomicPrimes
theorem _root_.solution {ι : Type} (f : ι → ℝ) (A B C : Set ι) (hB : B.Finite) (h : C ⊆ A ∪ B)
    (hA : Summable fun x : A => f x) : Summable fun x : C => f x := by
  have h1 : Summable (f ∘ ((↑) : ↥(A ∪ B) → ι)) := by
    rw [← Set.union_diff_self]
    exact (HasSum.add_disjoint Set.disjoint_sdiff_right hA.hasSum ((hB.subset Set.diff_subset).summable f).hasSum).summable
  exact h1.comp_injective (i := Set.inclusion h) (Set.inclusion_injective h)
end GlobalTheory.CyclotomicPrimes
