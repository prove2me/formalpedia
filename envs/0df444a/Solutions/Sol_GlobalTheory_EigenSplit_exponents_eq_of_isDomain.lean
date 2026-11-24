-- Prove2me | solution 1 for GlobalTheory.EigenSplit.exponents_eq_of_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:25:03.918223+00:00
-- url     : https://prove2.me/submissions/0d0120f1-4d0f-4fc9-a118-c0a26ddc3154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul

set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  {N : Type*} [AddCommGroup N] [Module R N]
namespace GlobalTheory.EigenSplit
theorem _root_.solution [IsDomain R] {σ : ι → O →+* R} (hσ : Function.Injective σ)
    (r s : ι → ℕ) (hrs : ∀ a, ∏ i, (X - C (σ i a)) ^ r i = ∏ i, (X - C (σ i a)) ^ s i) :
    r = s := by
  classical
  have hli : LinearIndependent R fun i => (σ i : O → R) :=
    (linearIndependent_monoidHom O R).comp (fun i => (σ i : O →* R))
      fun i j hij => hσ (RingHom.ext fun a => DFunLike.congr_fun hij a)
  have hcast : ∀ r s : ι → ℕ,
      (∀ a, ∏ i, (X - C (σ i a)) ^ r i = ∏ i, (X - C (σ i a)) ^ s i) →
      ∀ i, (r i : R) = s i := by
    intro r s hrs
    have hn : ∀ (r : ι → ℕ) a, (∏ i, (X - C (σ i a)) ^ r i).nextCoeff
        = -∑ i, (r i : R) * σ i a := by
      intro r a
      rw [Monic.nextCoeff_prod _ _ fun i _ => (monic_X_sub_C _).pow _, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(monic_X_sub_C _).nextCoeff_pow, nextCoeff_X_sub_C]
      simp
    refine Fintype.linearIndependent_iffₛ.1 hli _ _ ?_
    ext a
    have := congrArg nextCoeff (hrs a)
    rw [hn, hn, neg_inj] at this
    simpa using this
  obtain ⟨p, hp⟩ := CharP.exists R
  rcases CharP.char_is_prime_or_zero R p with hpp | rfl
  · have : Fact p.Prime := ⟨hpp⟩
    induction hn : ∑ i, (r i + s i) using Nat.strong_induction_on generalizing r s with
    | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · ext i
        have := Finset.sum_eq_zero_iff.1 hn i (Finset.mem_univ i)
        omega
      have hmod : ∀ i, r i % p = s i % p := fun i =>
        (CharP.natCast_eq_natCast R p).1 (hcast r s hrs i)
      have hdec : ∀ (r : ι → ℕ) a, ∏ i, (X - C (σ i a)) ^ r i
          = (∏ i, (X - C (σ i a)) ^ (r i % p)) * (∏ i, (X - C (σ i a)) ^ (r i / p)) ^ p := by
        intro r a
        rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← pow_mul, ← pow_add, mul_comm, Nat.mod_add_div]
      have hdiv : (fun i => r i / p) = fun i => s i / p := by
        refine ih (∑ i, (r i / p + s i / p)) ?_ _ _ (fun a => ?_) rfl
        · have h2 : 2 * ∑ i, (r i / p + s i / p) ≤ n := by
            rw [← hn, Finset.mul_sum]
            refine Finset.sum_le_sum fun i _ => ?_
            have h1 := Nat.mul_div_le (r i) p
            have h2 := Nat.mul_div_le (s i) p
            have h3 := hpp.two_le
            nlinarith [Nat.mul_le_mul_right (r i / p) h3, Nat.mul_le_mul_right (s i / p) h3]
          omega
        · have h1 := hrs a
          rw [hdec r, hdec s] at h1
          simp only [hmod] at h1
          have h2 := mul_left_cancel₀
            (monic_prod_of_monic _ _ fun i _ => (monic_X_sub_C _).pow _).ne_zero h1
          exact frobenius_inj R[X] p h2
      ext i
      rw [← Nat.mod_add_div (r i) p, ← Nat.mod_add_div (s i) p, hmod, congrFun hdiv i]
  · have := CharP.charP_to_charZero R
    ext i
    exact_mod_cast hcast r s hrs i
end GlobalTheory.EigenSplit
