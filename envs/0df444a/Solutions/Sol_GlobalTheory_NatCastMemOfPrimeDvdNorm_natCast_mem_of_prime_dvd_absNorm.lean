-- Prove2me | solution 1 for GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:28:26.048508+00:00
-- url     : https://prove2.me/submissions/96cdad88-d098-461b-aa63-636f412b4516

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NatCastMemOfPrimeDvdAbsNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatCastMemOfPrimeDvdNorm
open NumberField IsDedekindDomain
namespace GlobalTheory.NatCastMemOfPrimeDvdNorm
theorem _root_.solution {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (RingOfIntegers K)) {q : ℕ} (hq : Nat.Prime q)
    (hd : q ∣ Ideal.absNorm w.asIdeal) : (q : RingOfIntegers K) ∈ w.asIdeal := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (RingOfIntegers K ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  have hc : q ∣ Nat.card (RingOfIntegers K ⧸ w.asIdeal) := by
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' q hc
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have h1 : (q : RingOfIntegers K ⧸ w.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx]
    exact addOrderOf_nsmul_eq_zero x
  have h2 : (q : RingOfIntegers K ⧸ w.asIdeal) = 0 := (mul_eq_zero.mp h1).resolve_right hx0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2
end GlobalTheory.NatCastMemOfPrimeDvdNorm
