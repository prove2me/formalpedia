-- Prove2me | solution 1 for GlobalTheory.CondAway.isUnit_absNorm_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:35.614797+00:00
-- url     : https://prove2.me/submissions/2c4d9c7e-27ab-47d7-8e01-ee2757814da4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentConductorIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.CondAway
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.CondAway
theorem _root_.solution (q : HeightOneSpectrum (OF E)) (l : ℕ) (hl : l.Prime)
    (hq : (l : OF E) ∉ q.asIdeal) (O : Type) [CommRing O] [IsLocalRing O]
    (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O) : IsUnit ((Ideal.absNorm q.asIdeal : ℕ) : O) := by
  haveI : Finite (OF E ⧸ q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ q.ne_bot
  haveI := q.isMaximal
  letI : Field (OF E ⧸ q.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (OF E ⧸ q.asIdeal) := Fintype.ofFinite _
  obtain ⟨n, hp, hcard⟩ := FiniteField.card (OF E ⧸ q.asIdeal) (ringChar (OF E ⧸ q.asIdeal))
  set p := ringChar (OF E ⧸ q.asIdeal)
  have hN : Ideal.absNorm q.asIdeal = p ^ (n : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
  have hpl : p ≠ l := by
    intro h
    apply hq
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h]
    exact ringChar.Nat.cast_ringChar
  by_contra hu
  have hmem : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
    have : ((p : ℕ) : O) ^ (n : ℕ) ∈ IsLocalRing.maximalIdeal O := by
      rw [← Nat.cast_pow, ← hN]; exact (IsLocalRing.mem_maximalIdeal _).2 hu
    exact (IsLocalRing.maximalIdeal.isMaximal O).isPrime.mem_of_pow_mem _ this
  have hcop : IsCoprime (p : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hpl)
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    have := congrArg (Int.cast : ℤ → O) huv
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hlO)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
end GlobalTheory.CondAway
