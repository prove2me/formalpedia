-- Prove2me | solution 1 for GlobalTheory.PrimeOrderScalar.same_int_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:42:57.156353+00:00
-- url     : https://prove2.me/submissions/10357c85-370f-46d5-b8a5-13c28518bcfd

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ActsBySameInteger
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_zsmul_eq_zero_iff
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_exists_int_smul
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_not_isUnit_of_kills
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_int_dvd_of_mem

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
theorem _root_.solution {O : Type} [CommRing O] [IsLocalRing O] (ψ : O →+* S)
    (hT : T.Prime) (hA : Nat.card A = T) (hB : Nat.card B = T) (y : O) :
    ∃ k : ℤ, (∀ m : A, ψ y • m = k • m) ∧ ∀ m : B, ψ y • m = k • m := by
  obtain ⟨kA, hkA⟩ := exists_int_smul hT hA (ψ y)
  obtain ⟨kB, hkB⟩ := exists_int_smul hT hB (ψ y)
  have memA : y - (kA : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine not_isUnit_of_kills hT hA (u := ψ (y - kA)) (fun m => ?_) (hu.map ψ)
    rw [map_sub, map_intCast, sub_smul, hkA, Int.cast_smul_eq_zsmul, sub_self]
  have memB : y - (kB : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine not_isUnit_of_kills hT hB (u := ψ (y - kB)) (fun m => ?_) (hu.map ψ)
    rw [map_sub, map_intCast, sub_smul, hkB, Int.cast_smul_eq_zsmul, sub_self]
  have hTm : (T : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine not_isUnit_of_kills hT hB (u := ψ (T : O)) (fun m => ?_) (hu.map ψ)
    rw [map_natCast, Nat.cast_smul_eq_nsmul, ← hB]
    exact card_nsmul_eq_zero'
  have hd : ((kB - kA : ℤ) : O) ∈ IsLocalRing.maximalIdeal O := by
    have he : ((kB - kA : ℤ) : O) = (y - kA) - (y - kB) := by push_cast; ring
    rw [he]
    exact sub_mem memA memB
  have hdvd := int_dvd_of_mem (IsLocalRing.maximalIdeal.isMaximal O).ne_top hT hTm hd
  refine ⟨kA, hkA, fun m => ?_⟩
  have h0 := (zsmul_eq_zero_iff hT hB (kB - kA)).mpr hdvd m
  rw [sub_smul, sub_eq_zero] at h0
  rw [hkB, h0]
end GlobalTheory.PrimeOrderScalar
