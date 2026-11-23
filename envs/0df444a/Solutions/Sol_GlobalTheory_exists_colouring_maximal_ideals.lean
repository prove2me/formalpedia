-- Prove2me | solution 1 for GlobalTheory.exists_colouring_maximal_ideals
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:26.166457+00:00
-- url     : https://prove2.me/submissions/381a8f49-5252-420b-993b-01866b97d22e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr

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
theorem _root_.solution :
    ∃ c : Ideal (𝓞 K) → Fin (finrank ℚ K), ∀ p : ℕ, p.Prime → ∀ P Q : Ideal (𝓞 K),
      P.IsMaximal → Q.IsMaximal → (p : 𝓞 K) ∈ P → (p : 𝓞 K) ∈ Q → c P = c Q → P = Q := by
  classical
  haveI : Nonempty (Fin (finrank ℚ K)) := ⟨⟨0, finrank_pos⟩⟩
  have key : ∀ p : ℕ, ∃ e : Ideal (𝓞 K) → Fin (finrank ℚ K), p.Prime →
      Set.InjOn e {P | P.IsMaximal ∧ (p : 𝓞 K) ∈ P} := by
    intro p
    by_cases hp : p.Prime
    · have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
      haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
        ((Ideal.span_singleton_prime hp'.ne_zero).mpr hp').isMaximal hp0
      have hc := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hp0
      have hsub : {P : Ideal (𝓞 K) | P.IsMaximal ∧ (p : 𝓞 K) ∈ P} ⊆
          (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K) : Set _) := by
        rintro P ⟨hP, hpP⟩
        rw [mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hp0]
        refine ⟨hP.isPrime, ⟨hmax.eq_of_le ?_ ?_⟩⟩
        · exact Ideal.comap_ne_top _ hP.ne_top
        · rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
          simpa using hpP
      obtain ⟨e, -, he⟩ := Set.Finite.exists_injOn_of_encard_le
        (t := (Set.univ : Set (Fin (finrank ℚ K))))
        (Finset.finite_toSet (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K))) (by
          rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_univ]
          simpa using hc)
      exact ⟨e, fun _ => he.mono hsub⟩
    · exact ⟨fun _ => Classical.arbitrary _, fun h => absurd h hp⟩
  choose e he using key
  have hmin : ∀ p : ℕ, p.Prime → ∀ P : Ideal (𝓞 K), P.IsMaximal → (p : 𝓞 K) ∈ P →
      (Ideal.absNorm P).minFac = p := by
    intro p hp P hP hpP
    obtain ⟨q, n, hn, hqP, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    rw [H, hq.pow_minFac hn.ne']
    by_contra hne
    have hco : IsCoprime (q : 𝓞 K) (p : 𝓞 K) :=
      Nat.Coprime.cast ((Nat.coprime_primes hq hp).mpr hne)
    obtain ⟨a, b, hab⟩ := hco
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr
      (hab ▸ P.add_mem (P.mul_mem_left a hqP) (P.mul_mem_left b hpP)))
  refine ⟨fun P => e (Ideal.absNorm P).minFac P, fun p hp P Q hP hQ hpP hpQ h => ?_⟩
  simp only [hmin p hp P hP hpP, hmin p hp Q hQ hpQ] at h
  exact he p hp ⟨hP, hpP⟩ ⟨hQ, hpQ⟩ h
end GlobalTheory
