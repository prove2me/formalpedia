-- Prove2me | solution 1 for GlobalTheory.height_le_one_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:22.065801+00:00
-- url     : https://prove2.me/submissions/cbad6e72-76ab-4d98-bc46-d5cf39f3e74d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (m : Ideal B) [m.IsPrime] {f : B} (hf : f ≠ 0)
    (h : ∀ p : Ideal B, p.IsPrime → p ≠ ⊥ → p ≤ m → f ∈ p) : m.height ≤ 1 := by
  by_cases hm : m = ⊥
  · subst hm
    simp
  have hfin := (Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  have hsub : (m : Set B) ⊆ ⋃ P ∈ (Ideal.span {f}).minimalPrimes, ((id P : Ideal B) : Set B) := by
    intro x hx
    simp only [Set.mem_iUnion, id, SetLike.mem_coe]
    by_cases hx0 : x = 0
    · obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := m)
        ((Ideal.span_singleton_le_iff_mem _).mpr (h m inferInstance hm le_rfl))
      exact ⟨P, hP, hx0 ▸ P.zero_mem⟩
    obtain ⟨P, hP, hPm⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {x}) (J := m)
        ((Ideal.span_singleton_le_iff_mem _).mpr hx)
    have hPp : P.IsPrime := hP.1.1
    have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hP.1.2
    have hP1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
    have hfP : f ∈ P := h P hPp (fun e => hx0 (by simpa [e] using hxP)) hPm
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := P)
        ((Ideal.span_singleton_le_iff_mem _).mpr hfP)
    have hQp : Q.IsPrime := hQ.1.1
    have hfQ : f ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.1.2
    have hQ0 : ⊥ < Q := bot_lt_iff_ne_bot.mpr fun e => hf (by simpa [e] using hfQ)
    refine ⟨Q, hQ, ?_⟩
    rcases hQP.eq_or_lt with e | hlt
    · exact e ▸ hxP
    · exfalso
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hQ0
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h3 : (⊥ : Ideal B).height + 1 + 1 ≤ 1 := (add_le_add h1 le_rfl).trans (h2.trans hP1)
      simp at h3
      exact absurd h3 (by decide)
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime_finite hfin (f := id) ⊥ ⊥
    (fun i hi _ _ => hi.1.1)).mp hsub
  have hPp : P.IsPrime := hP.1.1
  exact (Ideal.height_mono hmP).trans
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)
end GlobalTheory
