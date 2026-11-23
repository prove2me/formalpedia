-- Prove2me | solution 1 for GlobalTheory.isHomogeneous_of_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:54.625243+00:00
-- url     : https://prove2.me/submissions/8dc5cb8b-57c7-4e70-a650-183730791f18

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {A : Type*} [CommRing A] {τ : Type*} [SetLike τ A] [AddSubgroupClass τ A]
  (𝒜 : ℕ → τ) [GradedRing 𝒜]
namespace GlobalTheory
theorem _root_.solution {J p : Ideal A} (hJ : J.IsHomogeneous 𝒜)
    (hp : p ∈ J.minimalPrimes) : p.IsHomogeneous 𝒜 := by
  have hpp : p.IsPrime := hp.1.1
  rw [Ideal.IsHomogeneous.iff_eq]
  refine le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _) ?_
  refine hp.2 ⟨hpp.homogeneousCore, ?_⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
  exact hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hp.1.2)
end GlobalTheory
