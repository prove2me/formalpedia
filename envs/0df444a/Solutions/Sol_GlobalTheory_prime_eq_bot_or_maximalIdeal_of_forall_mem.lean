-- Prove2me | solution 1 for GlobalTheory.prime_eq_bot_or_maximalIdeal_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:53.694879+00:00
-- url     : https://prove2.me/submissions/e8967baa-7a98-4201-9ff1-55fa460b6924

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
variable {B : Type*} [CommRing B] [IsDomain B]
variable [IsNoetherianRing B] [IsLocalRing B]
namespace GlobalTheory
theorem _root_.solution {f : B} (hf : f ≠ 0)
    (H : ∀ p : Ideal B, p.IsPrime → p ≠ ⊥ → f ∈ p) {p : Ideal B} (hp : p.IsPrime) :
    p = ⊥ ∨ p = maximalIdeal B := by
  classical
  refine or_iff_not_imp_left.mpr fun hp0 => ?_
  have hfin := (Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  have hmin : ∀ q : Ideal B, q.IsPrime → q ≠ ⊥ →
      ∃ P ∈ (Ideal.span {f}).minimalPrimes, P ≤ q := fun q hq hq0 =>
    Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem q).mpr (H q hq hq0))

  have hcover : ((maximalIdeal B : Ideal B) : Set B) ⊆
      ⋃ P ∈ (hfin.toFinset : Set (Ideal B)), ((id P : Ideal B) : Set B) := by
    intro x hx
    simp only [Set.Finite.coe_toFinset, id, Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    by_cases hx0 : x = 0
    · obtain ⟨P, hP, -⟩ := hmin p hp hp0
      exact ⟨P, hP, hx0 ▸ P.zero_mem⟩
    obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem (maximalIdeal B)).mpr hx)
    haveI hQp : Q.IsPrime := hQ.1.1
    have hxQ : x ∈ Q := (Ideal.span_singleton_le_iff_mem Q).mp hQ.1.2
    have hQ0 : Q ≠ ⊥ := fun h => hx0 (by simpa [h] using hxQ)
    have hQ1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
    obtain ⟨P, hP, hPQ⟩ := hmin Q hQp hQ0
    haveI hPp : P.IsPrime := hP.1.1
    have hfP : f ∈ P := (Ideal.span_singleton_le_iff_mem P).mp hP.1.2
    refine ⟨P, hP, ?_⟩
    rcases hPQ.eq_or_lt with h | h
    · exact h ▸ hxQ
    · have h1 : P.height < 1 := (Ideal.height_strict_mono_of_isPrime h).trans_le hQ1
      rw [ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
      exact absurd (by simpa [h1] using hfP) hf
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime (⊥ : Ideal B) ⊥ fun P hP _ _ =>
    ((Set.Finite.mem_toFinset hfin).mp hP).1.1).mp hcover
  have hP' := (Set.Finite.mem_toFinset hfin).mp hP
  have hpm : p ≤ maximalIdeal B := le_maximalIdeal hp.ne_top
  exact le_antisymm hpm (hmP.trans (hP'.2
    ⟨hp, (Ideal.span_singleton_le_iff_mem p).mpr (H p hp hp0)⟩ (hpm.trans hmP)))
end GlobalTheory
