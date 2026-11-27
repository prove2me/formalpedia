-- Prove2me | solution 1 for GlobalTheory.PrimeOrderScalar.int_dvd_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:32:54.949925+00:00
-- url     : https://prove2.me/submissions/6c7d77a5-485e-493b-a462-87b84d0021ea

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ActsBySameInteger
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open GlobalTheory GlobalTheory.PrimeOrderScalar
open scoped TensorProduct
variable {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] {T : ℕ}
namespace GlobalTheory.PrimeOrderScalar
theorem _root_.solution {R : Type} [CommRing R] {I : Ideal R} (hI : I ≠ ⊤) (hT : T.Prime)
    (hTI : (T : R) ∈ I) {n : ℤ} (hn : (n : R) ∈ I) : (T : ℤ) ∣ n := by
  by_contra h
  obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.mp hT).coprime_iff_not_dvd).mpr h
  apply hI
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a * (T : ℤ) + b * n : ℤ) : R) = 1 := by rw [hab]; simp
  rw [← h1]
  push_cast
  exact I.add_mem (I.mul_mem_left _ hTI) (I.mul_mem_left _ hn)
end GlobalTheory.PrimeOrderScalar
