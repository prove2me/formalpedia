-- Prove2me | solution 1 for Ideal.map_mem_minimalPrimes_span_singleton_of_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/cda4c5fe-2c95-58e8-bfcf-95692f3b5295

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_map_mem_minimalPrimes_span_singleton_of_apply_eq

set_option autoImplicit false

theorem solution
    {S : Type*} [CommRing S] (γ : S ≃+* S) (π : S) (hγπ : γ π = π)
    {P : Ideal S} (hP : P ∈ (Ideal.span {π}).minimalPrimes) :
    P.map (γ : S →+* S) ∈ (Ideal.span {π}).minimalPrimes := by

  have key : ∀ (e : S ≃+* S), e π = π → ∀ Q ∈ (Ideal.span {π}).minimalPrimes,
      Q.map (e : S →+* S) ∈ (Ideal.span {π}).minimalPrimes := by
    intro e he Q hQ
    have hQp : Q.IsPrime := hQ.1.1
    have hle : Ideal.span {π} ≤ Q := hQ.1.2
    refine ⟨⟨Ideal.map_isPrime_of_equiv e, ?_⟩, ?_⟩
    · rw [Ideal.span_singleton_le_iff_mem, ← he]
      exact Ideal.mem_map_of_mem _ ((Ideal.span_singleton_le_iff_mem _).mp hle)
    · rintro q ⟨hq, hπq⟩ hqle

      have hq' : (q.map ((e.symm : S ≃+* S) : S →+* S)).IsPrime := Ideal.map_isPrime_of_equiv e.symm
      have hπq' : Ideal.span {π} ≤ q.map ((e.symm : S ≃+* S) : S →+* S) := by
        rw [Ideal.span_singleton_le_iff_mem]
        have : e.symm π = π := by rw [← he, RingEquiv.symm_apply_apply, he]
        rw [← this]
        exact Ideal.mem_map_of_mem _ ((Ideal.span_singleton_le_iff_mem _).mp hπq)
      have hq'le : q.map ((e.symm : S ≃+* S) : S →+* S) ≤ Q := by
        have := Ideal.map_mono (f := ((e.symm : S ≃+* S) : S →+* S)) hqle
        rwa [Ideal.map_map, show ((e.symm : S ≃+* S) : S →+* S).comp (e : S →+* S) = RingHom.id S from by
          ext x; simp, Ideal.map_id] at this
      have heq : q.map ((e.symm : S ≃+* S) : S →+* S) = Q := le_antisymm hq'le (hQ.2 ⟨hq', hπq'⟩ hq'le)

      have := congrArg (Ideal.map (e : S →+* S)) heq
      rw [Ideal.map_map, show (e : S →+* S).comp ((e.symm : S ≃+* S) : S →+* S) = RingHom.id S from by
          ext x; simp, Ideal.map_id] at this
      exact this.symm.le
  exact key γ hγπ P hP

end S_Ideal_map_mem_minimalPrimes_span_singleton_of_apply_eq
end P2MW
export P2MW.S_Ideal_map_mem_minimalPrimes_span_singleton_of_apply_eq (solution)
