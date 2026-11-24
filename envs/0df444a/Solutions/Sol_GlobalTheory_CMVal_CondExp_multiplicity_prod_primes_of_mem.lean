-- Prove2me | solution 1 for GlobalTheory.CMVal.CondExp.multiplicity_prod_primes_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:58.731066+00:00
-- url     : https://prove2.me/submissions/793eda72-dd35-4fb6-8393-43d80282d20a

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConductorTimesSplitPrimesExponents
import Theorems.Thm_GlobalTheory_CMVal_CondExp_dvd_prod_primes_iff
import Theorems.Thm_GlobalTheory_CMVal_CondExp_prod_primes_ne_zero
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.CondExp
namespace GlobalTheory.CMVal.CondExp
theorem _root_.solution {R : Type} [CommRing R] [IsDedekindDomain R]
    (Q : Finset (HeightOneSpectrum R)) (v : HeightOneSpectrum R) (hv : v ∈ Q) :
    multiplicity v.asIdeal (∏ q ∈ Q, q.asIdeal) = 1 := by
  classical
  have h0 := prod_primes_ne_zero Q
  rw [← Finset.mul_prod_erase Q _ hv] at h0 ⊢
  rw [multiplicity_mul v.prime (FiniteMultiplicity.of_prime_left v.prime h0), multiplicity_self,
    multiplicity_eq_zero.2 (by rw [dvd_prod_primes_iff]; simp)]
end GlobalTheory.CMVal.CondExp
