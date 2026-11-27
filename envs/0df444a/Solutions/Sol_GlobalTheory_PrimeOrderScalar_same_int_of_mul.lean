-- Prove2me | solution 1 for GlobalTheory.PrimeOrderScalar.same_int_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:43:04.16934+00:00
-- url     : https://prove2.me/submissions/da995a32-02a8-4abd-bf7e-11f998c625fb

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ActsBySameInteger
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_zsmul_eq_zero_iff
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_exists_int_smul

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
variable {A B : Type} [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
namespace GlobalTheory.PrimeOrderScalar
theorem _root_.solution (hT : T.Prime) (hA : Nat.card A = T) (hB : Nat.card B = T)
    (X C D : S) (δ γ : ℤ) (hDA : ∀ m : A, D • m = δ • m) (hDB : ∀ m : B, D • m = δ • m)
    (hCA : ∀ m : A, C • m = γ • m) (hCB : ∀ m : B, C • m = γ • m)
    (hXA : ∀ m : A, D • X • m = C • m) (hXB : ∀ m : B, D • X • m = C • m)
    (hδ : ¬ (T : ℤ) ∣ δ) :
    ∃ k : ℤ, (∀ m : A, X • m = k • m) ∧ ∀ m : B, X • m = k • m := by
  obtain ⟨kA, hkA⟩ := exists_int_smul hT hA X
  obtain ⟨kB, hkB⟩ := exists_int_smul hT hB X
  have h1 : (T : ℤ) ∣ δ * kA - γ := by
    refine (zsmul_eq_zero_iff hT hA _).mp fun m => ?_
    have := hXA m
    rw [hkA, hDA, hCA, smul_smul] at this
    rw [sub_smul, this, sub_self]
  have h2 : (T : ℤ) ∣ δ * kB - γ := by
    refine (zsmul_eq_zero_iff hT hB _).mp fun m => ?_
    have := hXB m
    rw [hkB, hDB, hCB, smul_smul] at this
    rw [sub_smul, this, sub_self]
  have h3 : (T : ℤ) ∣ δ * (kB - kA) := by
    have he : δ * (kB - kA) = (δ * kB - γ) - (δ * kA - γ) := by ring
    rw [he]
    exact dvd_sub h2 h1
  have h4 : (T : ℤ) ∣ kB - kA :=
    ((Nat.prime_iff_prime_int.mp hT).dvd_or_dvd h3).resolve_left hδ
  refine ⟨kA, hkA, fun m => ?_⟩
  have h0 := (zsmul_eq_zero_iff hT hB (kB - kA)).mpr h4 m
  rw [sub_smul, sub_eq_zero] at h0
  rw [hkB, h0]
end GlobalTheory.PrimeOrderScalar
