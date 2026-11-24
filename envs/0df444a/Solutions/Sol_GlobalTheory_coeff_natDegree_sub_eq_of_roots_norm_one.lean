-- Prove2me | solution 1 for GlobalTheory.coeff_natDegree_sub_eq_of_roots_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:31:31.495184+00:00
-- url     : https://prove2.me/submissions/b16eacf1-d123-414f-bc9a-5e6ec5660a84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonicCoeffNatDegreeSubEqMulCmConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (Q : ℂ[X]) (hQ : Q.Monic)
    (hroots : ∀ z ∈ Q.roots, ‖z‖ = 1) :
    ∀ i ≤ Q.natDegree, Q.coeff (Q.natDegree - i) = Q.coeff 0 * starRingEnd ℂ (Q.coeff i) := by
  intro i hi
  set s := Q.roots with hs
  have hprod : (s.map fun z => X - C z).prod = Q := by
    have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := Q) IsAlgClosed.card_roots_eq_natDegree
    rwa [hQ.leadingCoeff, C_1, one_mul] at h
  have hrevX : ∀ z ∈ s, (X - C z : ℂ[X]).reverse = C (-z) * (X - C (starRingEnd ℂ z)) := by
    intro z hz
    have hz1 : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hroots z hz]; simp
    rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, ← one_mul (X : ℂ[X]), reverse_mul_X, ← C_1, reverse_C]
    rw [mul_sub, ← C_mul, neg_mul, hz1]
    simp only [C_1, C_neg, one_mul, pow_one]
    ring
  have hrev : Q.reverse = C (Q.coeff 0) * Q.map (starRingEnd ℂ) := by
    have key : ∀ t : Multiset ℂ, (∀ z ∈ t, (X - C z : ℂ[X]).reverse = C (-z) * (X - C (starRingEnd ℂ z))) →
        (t.map fun z => X - C z).prod.reverse
          = (t.map fun z => C (-z) * (X - C (starRingEnd ℂ z))).prod := by
      intro t
      induction t using Multiset.induction_on with
      | empty => intro _; simpa using reverse_C (1 : ℂ)
      | cons a t ih =>
        intro h
        rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
          reverse_mul_of_domain, ih (fun z hz => h z (Multiset.mem_cons_of_mem hz)),
          h a (Multiset.mem_cons_self a t)]
    conv_lhs => rw [← hprod]
    rw [key s hrevX, Multiset.prod_map_mul]
    conv_rhs => rw [← hprod]
    congr 1
    · rw [coeff_zero_multiset_prod, Multiset.map_map, map_multiset_prod, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro z _
      simp
    · rw [Polynomial.map_multiset_prod, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro z _
      simp
  have h1 := congrArg (fun p => p.coeff i) hrev
  simp only [coeff_reverse, coeff_C_mul, coeff_map] at h1
  rwa [revAt_le hi] at h1
end GlobalTheory
