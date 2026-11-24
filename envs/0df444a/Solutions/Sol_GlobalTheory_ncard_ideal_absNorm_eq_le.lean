-- Prove2me | solution 1 for GlobalTheory.ncard_ideal_absNorm_eq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:58.92371+00:00
-- url     : https://prove2.me/submissions/f0894d21-7bf7-44b8-ab50-1ba9c7855e5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Theorems.Thm_GlobalTheory_card_finMulAntidiag_eq_zeta_pow
import Theorems.Thm_GlobalTheory_exists_colouring_maximal_ideals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Real NumberField ArithmeticFunction.zeta
open Module NumberField Finset
open GlobalTheory
variable (K : Type*) [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) :
    {I : Ideal (𝓞 K) | Ideal.absNorm I = n}.ncard
      ≤ (ζ ^ finrank ℚ K : ArithmeticFunction ℕ) n := by
  classical
  obtain ⟨c, hc⟩ := exists_colouring_maximal_ideals K

  have key : ∀ (P : Ideal (𝓞 K)) (p f : ℕ), P.IsMaximal → p.Prime → (p : 𝓞 K) ∈ P →
      Ideal.absNorm P = p ^ f → ∀ s : Multiset (Ideal (𝓞 K)), (∀ Q ∈ s, Q.IsMaximal) →
      ((s.filter (fun Q => c Q = c P)).map Ideal.absNorm).prod ≠ 0 ∧
      (((s.filter (fun Q => c Q = c P)).map Ideal.absNorm).prod).factorization p
        = f * s.count P := by
    intro P p f hP hp hpP hN s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons Q s ih =>
      intro hs
      obtain ⟨ih0, ih⟩ := ih fun R hR => hs R (Multiset.mem_cons_of_mem hR)
      haveI hQ : Q.IsMaximal := hs Q (Multiset.mem_cons_self Q s)
      obtain ⟨q, g, hg, hqQ, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q
      have hQ0 : Ideal.absNorm Q ≠ 0 := H ▸ pow_ne_zero _ hq.ne_zero
      by_cases hcol : c Q = c P
      · rw [Multiset.filter_cons_of_pos (p := fun Q => c Q = c P) s hcol, Multiset.map_cons,
          Multiset.prod_cons, Nat.factorization_mul hQ0 ih0, Finsupp.add_apply, ih]
        refine ⟨mul_ne_zero hQ0 ih0, ?_⟩
        by_cases hQP : Q = P
        · subst hQP
          rw [Multiset.count_cons_self, hN, hp.factorization_pow, Finsupp.single_eq_same]
          ring
        · rw [Multiset.count_cons_of_ne (Ne.symm hQP), H, hq.factorization_pow,
            Finsupp.single_apply, if_neg, zero_add]
          rintro rfl
          exact hQP (hc q hq Q P hQ hP hqQ hpP hcol)
      · rw [Multiset.filter_cons_of_neg (p := fun Q => c Q = c P) s hcol]
        have hQP : P ≠ Q := by rintro rfl; exact hcol rfl
        rw [Multiset.count_cons_of_ne hQP]
        exact ⟨ih0, ih⟩
  have hprod : ∀ s : Multiset (Ideal (𝓞 K)),
      ∏ i, ((s.filter (fun Q => c Q = i)).map Ideal.absNorm).prod = Ideal.absNorm s.prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons Q s ih =>
      rw [Multiset.prod_cons, map_mul, ← ih]
      have : ∀ i, (((Q ::ₘ s).filter (fun Q => c Q = i)).map Ideal.absNorm).prod =
          (if c Q = i then Ideal.absNorm Q else 1) *
            ((s.filter (fun Q => c Q = i)).map Ideal.absNorm).prod := by
        intro i
        rw [Multiset.filter_cons]
        split_ifs <;> simp
      simp_rw [this]
      rw [prod_mul_distrib]
      simp
  have hmax : ∀ I : Ideal (𝓞 K), ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Q.IsMaximal := by
    intro I Q hQ
    have hQ' := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
    exact (Ideal.isPrime_of_prime hQ').isMaximal hQ'.ne_zero
  have hne : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n → I ≠ ⊥ := by
    rintro I hI rfl
    exact hn (by rw [← hI]; simp)
  rw [← card_finMulAntidiag_eq_zeta_pow, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn
    (fun I i => (((UniqueFactorizationMonoid.normalizedFactors I).filter
      (fun Q => c Q = i)).map Ideal.absNorm).prod) ?_ ?_ (Finset.finite_toSet _)
  · intro I hI
    rw [mem_coe, Nat.mem_finMulAntidiag, hprod, Ideal.prod_normalizedFactors_eq_self (hne I hI)]
    exact ⟨hI, hn⟩
  · intro I hI J hJ h
    rw [← Ideal.prod_normalizedFactors_eq_self (hne I hI),
      ← Ideal.prod_normalizedFactors_eq_self (hne J hJ)]
    congr 1
    ext P
    by_cases hP : P.IsMaximal
    · obtain ⟨p, f, hf, hpP, hp, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
      have h1 := (key P p f hP hp hpP H _ (hmax I)).2
      have h2 := (key P p f hP hp hpP H _ (hmax J)).2
      have h3 := congrFun h (c P)
      simp only at h3
      rw [h3, h2] at h1
      exact (Nat.eq_of_mul_eq_mul_left hf h1).symm
    · rw [Multiset.count_eq_zero_of_notMem fun h => hP (hmax I P h),
        Multiset.count_eq_zero_of_notMem fun h => hP (hmax J P h)]
end GlobalTheory
