-- Prove2me | solution 1 for GlobalTheory.CMVal.CondExp.condQ_exponents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:20:24.412025+00:00
-- url     : https://prove2.me/submissions/d8747209-8e0b-4e5f-af82-ee0b4db72666

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConductorTimesSplitPrimesExponents
import Theorems.Thm_GlobalTheory_CMVal_CondExp_dvd_prod_primes_iff
import Theorems.Thm_GlobalTheory_CMVal_CondExp_prod_primes_ne_zero
import Theorems.Thm_GlobalTheory_CMVal_CondExp_multiplicity_prod_primes_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.CondExp
namespace GlobalTheory.CMVal.CondExp
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → condQ 𝔣 Q ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ condQ 𝔣 Q → Splits v) ∧ (∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v ≠ 0 → v.asIdeal ∣ condQ 𝔣 Q) ∧ (∀ v ∈ Q, expIn (condQ 𝔣 Q) v = 1) ∧ (∀ v ∉ Q, expIn (condQ 𝔣 Q) v = expIn 𝔣 v) ∧ {v : HeightOneSpectrum (OF E) | expIn (condQ 𝔣 Q) v ≠ 0}.Finite := by
  intro E _ _ 𝔣 Q hb ha
  have h0 : condQ 𝔣 Q ≠ 0 := mul_ne_zero hb.1 (prod_primes_ne_zero Q)
  have hm : ∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v =
      expIn 𝔣 v + multiplicity v.asIdeal (∏ q ∈ Q, q.asIdeal) := fun v =>
    multiplicity_mul v.prime (FiniteMultiplicity.of_prime_left v.prime h0)
  have hd : ∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v ≠ 0 → v.asIdeal ∣ condQ 𝔣 Q := by
    intro v hv
    by_contra h
    exact hv (multiplicity_eq_zero.2 h)
  refine ⟨h0, ?_, hd, ?_, ?_, (Ideal.finite_factors h0).subset hd⟩
  · intro v hv
    rcases v.prime.dvd_or_dvd hv with h | h
    · exact (hb.2.2 v h).1
    · exact (ha v ((dvd_prod_primes_iff Q v).1 h)).1
  · intro v hv
    have h1 : expIn 𝔣 v = 0 := multiplicity_eq_zero.2 (ha v hv).2
    rw [hm, h1, multiplicity_prod_primes_of_mem Q v hv]
  · intro v hv
    rw [hm, multiplicity_eq_zero.2 (fun h => hv ((dvd_prod_primes_iff Q v).1 h)), add_zero]
end GlobalTheory.CMVal.CondExp
