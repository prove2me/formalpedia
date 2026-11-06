-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.lambda_not_dvd_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:19:47.055806+00:00
-- url     : https://prove2.me/submissions/c2d11a29-27ae-44fd-b6ad-db1d65f7cc0b

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution : ¬ lambda ∣ (2 : O) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hprime : Prime lambda :=
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'
  let I : Ideal O := Ideal.span {lambda}
  have hI : I.IsMaximal := by
    have hp : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hprime
    have hne : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hprime.ne_zero
    exact hp.isMaximal hne
  let : I.IsMaximal := hI
  let : Field (O ⧸ I) := Ideal.Quotient.field I
  let : Fintype (O ⧸ I) := Fintype.ofFinite _
  have hcard : Nat.card (O ⧸ I) = 3 := by
    change Nat.card (O ⧸ Ideal.span {omega - 1}) = 3
    rw [omega,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).card_quotient_toInteger_sub_one,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).norm_toInteger_sub_one_of_prime_ne_two'
        (by decide)]
    norm_num
  intro hdiv
  have hmem : (2 : O) ∈ I := (Ideal.mem_span_singleton).mpr hdiv
  have hzero : (2 : O ⧸ I) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  have hchar : ringChar (O ⧸ I) = 2 := by
    have hdvd : ringChar (O ⧸ I) ∣ 2 := (ringChar.spec (O ⧸ I) 2).mp hzero
    exact (Nat.prime_dvd_prime_iff_eq
      (CharP.char_is_prime (O ⧸ I) (ringChar (O ⧸ I))) Nat.prime_two).mp hdvd
  have heven := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card, hcard] at heven
  norm_num at heven
end OAI.ActualEisensteinCubic
