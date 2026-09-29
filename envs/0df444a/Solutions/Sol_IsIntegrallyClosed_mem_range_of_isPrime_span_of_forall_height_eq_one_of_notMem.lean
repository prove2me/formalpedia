-- Prove2me | solution 1 for IsIntegrallyClosed.mem_range_of_isPrime_span_of_forall_height_eq_one_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/07f7619e-8a8f-5ef1-ba95-9003ab7fe9a0

import Mathlib
import Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_mem_range_of_isPrime_span_of_forall_height_eq_one_of_notMem

set_option autoImplicit false

theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {F : Type*} [Field F] (ι : B →+* F) (hι : Function.Injective ι)
    (ϖ : B) (hϖ : ϖ ≠ 0) (hprime : (Ideal.span {ϖ}).IsPrime)
    (x : F)
    (hV : ∃ a s : B, s ∉ Ideal.span {ϖ} ∧ x * ι s = ι a)
    (hH : ∀ P : Ideal B, P.IsPrime → P.height = 1 → ϖ ∉ P → ∃ a s : B, s ∉ P ∧ x * ι s = ι a) :
    x ∈ ι.range := by
  classical

  have hvert : ∀ (P : Ideal B) [P.IsPrime], P.height = 1 → ϖ ∈ P → P = Ideal.span {ϖ} := by
    intro P _ hP hmem
    have hle : Ideal.span {ϖ} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr hmem
    have h1 : 1 ≤ (Ideal.span {ϖ}).height :=
      Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ)
    haveI := hprime
    exact (Ideal.eq_of_le_of_height_le (I := Ideal.span {ϖ}) (J := P) hle (by rw [hP]; exact h1)).symm

  let K := FractionRing B
  let j : K →+* F := IsFractionRing.lift hι
  have hj : ∀ b : B, j (algebraMap B K b) = ι b := fun b => IsFractionRing.lift_algebraMap hι b
  have hjinj : Function.Injective j := j.injective
  obtain ⟨a₀, s₀, hs₀, hx₀⟩ := hV
  have hs₀0 : s₀ ≠ 0 := by
    rintro rfl
    exact hs₀ (Ideal.zero_mem _)
  have hιs₀ : ι s₀ ≠ 0 := fun h => hs₀0 (hι (by rw [h, map_zero]))
  set x' : K := algebraMap B K a₀ / algebraMap B K s₀ with hx'
  have hjx' : j x' = x := by
    rw [hx', map_div₀, hj, hj, div_eq_iff hιs₀, hx₀]
  have key : ∀ (a s : B), x * ι s = ι a → x' * algebraMap B K s = algebraMap B K a := by
    intro a s h
    apply hjinj
    rw [map_mul, hjx', hj, hj, h]
  have hx : ∀ (P : Ideal B) [P.IsPrime], P.height = 1 →
      ∃ r s : B, s ∉ P ∧ x' * algebraMap B K s = algebraMap B K r := by
    intro P _ hP
    by_cases hmem : ϖ ∈ P
    · have hPeq : P = Ideal.span {ϖ} := hvert P hP hmem
      refine ⟨a₀, s₀, ?_, key a₀ s₀ hx₀⟩
      rw [hPeq]; exact hs₀
    · obtain ⟨a, s, hs, h⟩ := hH P inferInstance hP hmem
      exact ⟨a, s, hs, key a s h⟩
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one K x' hx
  refine ⟨r, ?_⟩
  rw [← hj, hr, hjx']

end S_IsIntegrallyClosed_mem_range_of_isPrime_span_of_forall_height_eq_one_of_notMem
end P2MW
export P2MW.S_IsIntegrallyClosed_mem_range_of_isPrime_span_of_forall_height_eq_one_of_notMem (solution)
