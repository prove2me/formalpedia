-- Prove2me | solution 1 for MazurTransfer.mixed_single_section_reciprocal_recovery
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-15T05:09:57.891836+00:00
-- url     : https://prove2.me/submissions/8289b8cd-6a6d-4a4b-8e98-0a2884264392

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: exact integral identities recovering reciprocal coordinates
from the mixed single-section parameter and the inverse of p.
Named downstream consumer: the actual reciprocal principal-patch comparison.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.MixedSingleSectionReciprocalRecoveryProof
variable {A : Type*} [CommRing A]

theorem recovered_coordinate_identity (t p u : A) (hu : p * u = 1)
    (htp : t ^ 4 - p ^ 3 - p ^ 2 * t - t ^ 3 - p ^ 2 - p * t = 0) :
    t * (t * u) ^ 3 - (1 + t * u + (t * u) ^ 3) = (1 + t * u) * u := by
  have hp2 : p ^ 2 * u ^ 2 = 1 := by rw [← mul_pow,hu,one_pow]
  have hp3 : p ^ 3 * u ^ 3 = 1 := by rw [← mul_pow,hu,one_pow]
  linear_combination u ^ 3 * htp + hp3 + (t * u + u) * hp2 + t * u ^ 2 * hu

theorem recovered_reciprocal_equation (t p u : A) (hu : p * u = 1)
    (htp : t ^ 4 - p ^ 3 - p ^ 2 * t - t ^ 3 - p ^ 2 - p * t = 0) :
    ((1 + t * u) * u) ^ 2 + (1 + t * u + (t * u) ^ 3) * ((1 + t * u) * u) -
      ((t * u) ^ 4 + (t * u) ^ 5) = 0 := by
  have he := recovered_coordinate_identity t p u hu htp
  linear_combination -((1 + t * u) * u) * he

end MazurTransfer.MixedSingleSectionReciprocalRecoveryProof

theorem solution
    {A : Type*} [CommRing A] (t p u : A) (hu : p * u = 1)
    (htp : t ^ 4 - p ^ 3 - p ^ 2 * t - t ^ 3 - p ^ 2 - p * t = 0) :
    (t * (t * u) ^ 3 - (1 + t * u + (t * u) ^ 3) = (1 + t * u) * u) ∧
    (((1 + t * u) * u) ^ 2 + (1 + t * u + (t * u) ^ 3) * ((1 + t * u) * u) -
      ((t * u) ^ 4 + (t * u) ^ 5) = 0)  := by
  exact ⟨MazurTransfer.MixedSingleSectionReciprocalRecoveryProof.recovered_coordinate_identity t p u hu htp,
    MazurTransfer.MixedSingleSectionReciprocalRecoveryProof.recovered_reciprocal_equation t p u hu htp⟩
#print axioms solution
