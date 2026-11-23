-- Prove2me | solution 1 for GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable.finsum_quot_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:45.556332+00:00
-- url     : https://prove2.me/submissions/f630924f-9cd4-4b11-819c-6b5b91ee9f76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumCosetRepsNeZeroIffCommensurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable
namespace GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable
theorem _root_.solution {V K : Type} [AddCommGroup V] [Field K] (f : V → K) (M N : AddSubgroup V)
    (S : Finset V) (hMN : M ≤ N) (hidx : M.relIndex N ≠ 0)
    (hf : ∀ v, ∀ u ∈ N, f (v + u) = f v)
    (hinj : ∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s')
    (hcov : ∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) :
    ∑ᶠ c : V ⧸ M, f c.out = (M.relIndex N : K) * ∑ s ∈ S, f s := by
  classical
  haveI : Finite (N ⧸ M.addSubgroupOf N) := Nat.finite_of_card_ne_zero hidx
  letI : Fintype (N ⧸ M.addSubgroupOf N) := Fintype.ofFinite _
  let φ : V × (N ⧸ M.addSubgroupOf N) → V ⧸ M :=
    fun p => QuotientAddGroup.mk (p.1 + ((p.2.out : N) : V))
  have hout : ∀ v : V, f (QuotientAddGroup.mk v : V ⧸ M).out = f v := by
    intro v
    have h : -v + (QuotientAddGroup.mk v : V ⧸ M).out ∈ M := by
      rw [← QuotientAddGroup.eq]; simp
    have := hf v _ (hMN h)
    simpa using this
  rw [finsum_eq_sum_of_support_subset (s := (S ×ˢ Finset.univ).image φ)]
  · rw [Finset.sum_image]
    · rw [Finset.sum_product]
      have : ∀ s ∈ S, ∑ q : N ⧸ M.addSubgroupOf N, f (φ (s, q)).out = (M.relIndex N : K) * f s := by
        intro s _
        have : ∀ q : N ⧸ M.addSubgroupOf N, f (φ (s, q)).out = f s := by
          intro q
          simp only [φ]
          rw [hout, hf _ _ (q.out).2]
        simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Nat.card_eq_fintype_card]
        rfl
      rw [Finset.sum_congr rfl this, Finset.mul_sum]
    · rintro ⟨s, q⟩ hp ⟨s', q'⟩ hp' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
      simp only [φ, QuotientAddGroup.eq] at h
      have hs : s = s' := by
        apply hinj s hp.1 s' hp'.1
        have h1 := N.add_mem (N.sub_mem (q'.out).2 (q.out).2) (N.neg_mem (hMN h))
        convert h1 using 1
        abel
      subst hs
      have hq : q = q' := by
        rw [← Quotient.out_eq q, ← Quotient.out_eq q']
        apply QuotientAddGroup.eq.2
        rw [AddSubgroup.mem_addSubgroupOf]
        convert h using 1
        push_cast
        abel
      rw [hq]
  · intro c hc
    obtain ⟨s, hs, hn⟩ := hcov c.out hc
    simp only [Finset.coe_image, Set.mem_image]
    refine ⟨(s, QuotientAddGroup.mk ⟨c.out - s, hn⟩), by simp [hs], ?_⟩
    have h : -(QuotientAddGroup.mk (⟨c.out - s, hn⟩ : N) : N ⧸ M.addSubgroupOf N).out
        + (⟨c.out - s, hn⟩ : N) ∈ M.addSubgroupOf N := by
      rw [← QuotientAddGroup.eq]; simp
    rw [AddSubgroup.mem_addSubgroupOf] at h
    conv_rhs => rw [← Quotient.out_eq c]
    apply QuotientAddGroup.eq.2
    convert h using 1
    push_cast
    abel
end GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable
