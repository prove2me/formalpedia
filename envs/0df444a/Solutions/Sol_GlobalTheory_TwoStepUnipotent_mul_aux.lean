-- Prove2me | solution 1 for GlobalTheory.TwoStepUnipotent.mul_aux
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:42:26.763802+00:00
-- url     : https://prove2.me/submissions/53455f6b-5f68-4a09-a8eb-60862d791b4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory GlobalTheory.TwoStepUnipotent
variable {S : Type} [Ring S] (st : S →+ S) (e₁ e₃ h : S)
variable {st e₁ e₃ h}
namespace GlobalTheory.TwoStepUnipotent
theorem _root_.solution {b c z b' c' z' : S} (h31 : e₃ * e₁ = 0)
    (h1 : b * e₃ = b) (h2 : z * e₃ = z) (h3 : e₃ * b' = 0) (h4 : e₁ * c' = c')
    (h5 : e₁ * z' = z') (h6 : c * e₁ = 0) :
    (1 - c + b + z) * (1 - c' + b' + z') = 1 - (c + c') + (b + b') + (z + z' - c * b') := by
  have k1 : c * c' = 0 := by
    calc c * c' = c * e₁ * c' := by rw [mul_assoc, h4]
      _ = 0 := by rw [h6, zero_mul]
  have k2 : c * z' = 0 := by
    calc c * z' = c * e₁ * z' := by rw [mul_assoc, h5]
      _ = 0 := by rw [h6, zero_mul]
  have k3 : b * c' = 0 := by
    calc b * c' = b * e₃ * (e₁ * c') := by rw [h1, h4]
      _ = b * (e₃ * e₁) * c' := by simp only [mul_assoc]
      _ = 0 := by rw [h31, mul_zero, zero_mul]
  have k4 : b * b' = 0 := by
    calc b * b' = b * e₃ * b' := by rw [h1]
      _ = 0 := by rw [mul_assoc, h3, mul_zero]
  have k5 : b * z' = 0 := by
    calc b * z' = b * e₃ * (e₁ * z') := by rw [h1, h5]
      _ = b * (e₃ * e₁) * z' := by simp only [mul_assoc]
      _ = 0 := by rw [h31, mul_zero, zero_mul]
  have k6 : z * c' = 0 := by
    calc z * c' = z * e₃ * (e₁ * c') := by rw [h2, h4]
      _ = z * (e₃ * e₁) * c' := by simp only [mul_assoc]
      _ = 0 := by rw [h31, mul_zero, zero_mul]
  have k7 : z * b' = 0 := by
    calc z * b' = z * e₃ * b' := by rw [h2]
      _ = 0 := by rw [mul_assoc, h3, mul_zero]
  have k8 : z * z' = 0 := by
    calc z * z' = z * e₃ * (e₁ * z') := by rw [h2, h5]
      _ = z * (e₃ * e₁) * z' := by simp only [mul_assoc]
      _ = 0 := by rw [h31, mul_zero, zero_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, k1, k2, k3, k4, k5, k6, k7, k8]
  abel
end GlobalTheory.TwoStepUnipotent
