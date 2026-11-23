-- Prove2me | solution 1 for GlobalTheory.exists_homogeneous_forall_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:18:15.079474+00:00
-- url     : https://prove2.me/submissions/cd6c5d0a-437a-4f77-8f19-435d3c1bca32

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Theorems.Thm_GlobalTheory_exists_homogeneous_notMem_of_not_le

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
theorem _root_.solution (s : Finset (Ideal A))
    (hprime : ∀ p ∈ s, p.IsPrime) (hhom : ∀ p ∈ s, p.IsHomogeneous 𝒜)
    (hinc : ∀ p ∈ s, ∀ q ∈ s, q ≤ p → q = p)
    (hpos : ∀ p ∈ s, ∃ n, 0 < n ∧ ∃ x ∈ 𝒜 n, x ∉ p) :
    ∃ n, 0 < n ∧ ∃ x ∈ 𝒜 n, ∀ p ∈ s, x ∉ p := by
  classical
  have key : ∀ p : s, ∃ n, 0 < n ∧ ∃ g ∈ 𝒜 n, g ∉ p.1 ∧ ∀ q ∈ s, q ≠ p.1 → g ∈ q := by
    rintro ⟨p, hp⟩
    obtain ⟨n, hn, x, hx, hxp⟩ := hpos p hp
    have hH : ((s.erase p).inf id).IsHomogeneous 𝒜 := by
      rw [Finset.inf_eq_iInf]
      exact Ideal.IsHomogeneous.iInf₂ fun q hq => hhom q (Finset.mem_of_mem_erase hq)
    have hnle : ¬ (s.erase p).inf id ≤ p := by
      rw [(hprime p hp).inf_le']
      rintro ⟨q, hq, hqp⟩
      exact (Finset.ne_of_mem_erase hq) (hinc p hp q (Finset.mem_of_mem_erase hq) hqp)
    obtain ⟨m, y, hy, hyJ, hyp⟩ := exists_homogeneous_notMem_of_not_le 𝒜 hH hnle
    refine ⟨n + m, by omega, x * y, SetLike.mul_mem_graded hx hy, ?_, ?_⟩
    · intro h
      exact ((hprime p hp).mem_or_mem h).elim hxp hyp
    · intro q hq hqp
      exact q.mul_mem_left _
        ((Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨hqp, hq⟩) : _ ≤ q) hyJ)
  choose n hn g hg hgp hgq using key
  have hD : 0 < ∏ p, n p := Finset.prod_pos fun p _ => hn p
  have hdvd : ∀ p, n p ∣ ∏ p, n p := fun p => Finset.dvd_prod_of_mem _ (Finset.mem_univ p)
  have hq0 : ∀ p, (∏ p, n p) / n p ≠ 0 := fun p =>
    (Nat.div_pos (Nat.le_of_dvd hD (hdvd p)) (hn p)).ne'
  refine ⟨∏ p, n p, hD, ∑ p, g p ^ ((∏ p, n p) / n p), ?_, ?_⟩
  · refine sum_mem fun p _ => ?_
    have := SetLike.pow_mem_graded ((∏ p, n p) / n p) (hg p)
    rwa [smul_eq_mul, Nat.div_mul_cancel (hdvd p)] at this
  · intro p hp hmem
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨p, hp⟩ : s))] at hmem
    have h2 : ∑ q ∈ Finset.univ.erase (⟨p, hp⟩ : s), g q ^ ((∏ p, n p) / n q) ∈ p := by
      refine p.sum_mem fun q hq => Ideal.pow_mem_of_mem _ ?_ _ (Nat.pos_of_ne_zero (hq0 q))
      refine hgq q p hp fun h => Finset.ne_of_mem_erase hq (Subtype.ext h.symm)
    have h3 := (Submodule.add_mem_iff_left p h2).mp hmem
    exact hgp ⟨p, hp⟩ ((hprime p hp).mem_of_pow_mem _ h3)
end GlobalTheory
