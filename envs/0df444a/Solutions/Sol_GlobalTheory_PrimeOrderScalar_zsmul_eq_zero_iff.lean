-- Prove2me | solution 1 for GlobalTheory.PrimeOrderScalar.zsmul_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:31:24.8785+00:00
-- url     : https://prove2.me/submissions/18ed3d77-485f-4797-b220-6098ac01d8a9

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ActsBySameInteger

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open GlobalTheory GlobalTheory.PrimeOrderScalar
open scoped TensorProduct
variable {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] {T : ℕ}
namespace GlobalTheory.PrimeOrderScalar
theorem _root_.solution (hT : T.Prime) (hM : Nat.card M = T) (n : ℤ) :
    (∀ m : M, n • m = 0) ↔ (T : ℤ) ∣ n := by
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; exact hT.ne_zero)
  constructor
  · intro h
    haveI : Nontrivial M :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hM]; exact hT.one_lt)
    obtain ⟨a, ha⟩ := exists_ne (0 : M)
    have hord : addOrderOf a = T := by
      have hdvd := addOrderOf_dvd_natCard a
      rw [hM] at hdvd
      rcases (Nat.dvd_prime hT).mp hdvd with h1 | h1
      · exfalso
        apply ha
        have := addOrderOf_nsmul_eq_zero a
        rwa [h1, one_smul] at this
      · exact h1
    rw [← hord]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr (h a)
  · rintro ⟨c, rfl⟩ m
    have hT0 : (T : ℤ) • m = 0 := by
      rw [natCast_zsmul, ← hM]
      exact card_nsmul_eq_zero'
    rw [mul_comm, mul_smul, hT0, smul_zero]
end GlobalTheory.PrimeOrderScalar
