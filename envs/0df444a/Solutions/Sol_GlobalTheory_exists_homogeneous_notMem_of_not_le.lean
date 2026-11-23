-- Prove2me | solution 1 for GlobalTheory.exists_homogeneous_notMem_of_not_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:00.439871+00:00
-- url     : https://prove2.me/submissions/6dd32a4a-1577-488d-b75f-f71583c7688b

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
    (h : ¬ J ≤ p) : ∃ n, ∃ x ∈ 𝒜 n, x ∈ J ∧ x ∉ p := by
  classical
  by_contra hcon
  push Not at hcon
  refine h fun x hx => ?_
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact p.sum_mem fun i _ => hcon i _ (SetLike.coe_mem _) (hJ i hx)
end GlobalTheory
