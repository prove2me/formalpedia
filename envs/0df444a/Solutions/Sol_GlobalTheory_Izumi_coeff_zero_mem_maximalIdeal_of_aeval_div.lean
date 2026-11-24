-- Prove2me | solution 1 for GlobalTheory.Izumi.coeff_zero_mem_maximalIdeal_of_aeval_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:57:32.704904+00:00
-- url     : https://prove2.me/submissions/f8ed44d3-2286-41d7-8a25-5c6d91f00e78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDominatingLocalDomainEqMulMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.Izumi
namespace GlobalTheory.Izumi
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsIntegrallyClosed R] (f G : R) (h : G ∉ Ideal.span {f}) (P : R[X])
    (hP : aeval (algebraMap R (FractionRing R) f / algebraMap R (FractionRing R) G) P = 0) :
    P.coeff 0 ∈ maximalIdeal R := by
  by_contra hc
  have hunit : IsUnit (P.coeff 0) := by
    simpa [mem_maximalIdeal] using hc
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hG : G ≠ 0 := by rintro rfl; exact h (zero_mem _)
  have hG' : algebraMap R (FractionRing R) G ≠ 0 := (map_ne_zero_iff _ hinj).2 hG
  have hf : f ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, ← coeff_zero_eq_aeval_zero'] at hP
    exact hunit.ne_zero ((map_eq_zero_iff _ hinj).1 hP)
  have hf' : algebraMap R (FractionRing R) f ≠ 0 := (map_ne_zero_iff _ hinj).2 hf
  set u := algebraMap R (FractionRing R) f / algebraMap R (FractionRing R) G with hu
  have hu0 : u ≠ 0 := div_ne_zero hf' hG'
  letI := invertibleOfNonzero hu0
  have hrev : aeval (⅟u) P.reverse = 0 := by
    rw [aeval_def, eval₂_reverse_eq_zero_iff]; exact hP
  have hint := isIntegral_leadingCoeff_smul P.reverse (⅟u) hrev
  rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero hunit.ne_zero] at hint
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  apply h
  rw [← Ideal.unit_mul_mem_iff_mem _ hunit, Ideal.mem_span_singleton']
  refine ⟨r, hinj ?_⟩
  rw [map_mul, map_mul, hr, invOf_eq_inv, hu, Algebra.smul_def]
  field_simp
end GlobalTheory.Izumi
