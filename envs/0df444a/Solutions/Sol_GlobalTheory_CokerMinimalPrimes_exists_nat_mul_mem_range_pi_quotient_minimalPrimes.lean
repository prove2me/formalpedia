-- Prove2me | solution 1 for GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:30:00.800724+00:00
-- url     : https://prove2.me/submissions/5b5e9b77-9f05-45d7-9472-4c4273435f2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNatMulMemRangePiQuotientMinimalPrimes
import Theorems.Thm_GlobalTheory_CokerMinimalPrimes_exists_nat_mem_sup
import Theorems.Thm_GlobalTheory_CokerMinimalPrimes_exists_pow_mul_mem_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CokerMinimalPrimes
namespace GlobalTheory.CokerMinimalPrimes
theorem _root_.solution : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], ∃ n : ℕ, n ≠ 0 ∧
    ∀ b' : ((P : minimalPrimes B) → B ⧸ (P : Ideal B)),
      (n : (P : minimalPrimes B) → B ⧸ (P : Ideal B)) * b' ∈
        (Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)).range := by
  intro B _ _
  classical
  haveI : IsNoetherian ℤ B := isNoetherian_of_isNoetherianRing_of_finite ℤ B
  haveI : IsNoetherianRing B := isNoetherian_of_tower ℤ inferInstance
  haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  letI : Fintype (minimalPrimes B) := Fintype.ofFinite _
  have hpair : ∀ P Q : minimalPrimes B, ∃ m : ℕ, m ≠ 0 ∧ (P ≠ Q → (m : B) ∈ (P : Ideal B) ⊔ Q) := by
    intro P Q
    by_cases h : P = Q
    · exact ⟨1, one_ne_zero, fun h' => (h' h).elim⟩
    obtain ⟨m, hm0, hm⟩ := exists_nat_mem_sup B P.2 Q.2 (fun e => h (Subtype.ext e))
    exact ⟨m, hm0, fun _ => hm⟩
  choose f hf0 hf using hpair
  let m : ℕ := ∏ p : minimalPrimes B × minimalPrimes B, f p.1 p.2
  have hm0 : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => hf0 p.1 p.2
  have hm : ∀ P Q : minimalPrimes B, P ≠ Q → (m : B) ∈ (P : Ideal B) ⊔ Q := by
    intro P Q hPQ
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p : minimalPrimes B × minimalPrimes B => f p.1 p.2)
      (Finset.mem_univ (P, Q))
    change ((∏ p : minimalPrimes B × minimalPrimes B, f p.1 p.2 : ℕ) : B) ∈ _
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hf P Q hPQ)
  refine ⟨m ^ (Fintype.card (minimalPrimes B) - 1), pow_ne_zero _ hm0, fun b' => ?_⟩
  obtain ⟨a, ha⟩ := exists_pow_mul_mem_range (fun P : minimalPrimes B => (P : Ideal B)) (m : B) hm b'
  refine ⟨a, funext fun P => ?_⟩
  change Ideal.Quotient.mk (P : Ideal B) a = _
  rw [ha P, Pi.mul_apply, Pi.natCast_apply, map_natCast]
  push_cast
  rfl
end GlobalTheory.CokerMinimalPrimes
