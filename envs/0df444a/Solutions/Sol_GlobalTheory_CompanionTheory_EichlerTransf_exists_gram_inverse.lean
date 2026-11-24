-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EichlerTransf.exists_gram_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:18:22.146829+00:00
-- url     : https://prove2.me/submissions/d793c52c-4b2e-4f0e-8423-8b26e96be8ee

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExtendByZeroApplyOfNe
import Theorems.Thm_GlobalTheory_CompanionTheory_EichlerTransf_isUnit_gram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EichlerTransf
open scoped ComplexOrder
variable {n m : ℕ}
namespace GlobalTheory.CompanionTheory.EichlerTransf
theorem _root_.solution (a : Matrix (Fin n) (Fin m) ℂ) (b : Matrix (Fin m) (Fin n) ℂ)
    (P : Matrix (Fin m) (Fin m) ℂ) (hPh : Pᴴ = P) (hPP : P * P = P) (hb : b * a = P)
    (hap : a * P = a) :
    ∃ C H : Matrix (Fin m) (Fin m) ℂ, C * H = P ∧ aᴴ * a * C = P ∧ C * P = C := by
  have hu := isUnit_gram a b P hPh hPP hb
  set H := aᴴ * a + (1 - P) with hH
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hl : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul _ hdet
  have hr : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hPa : P * aᴴ = aᴴ := by
    have := congrArg conjTranspose hap
    rwa [conjTranspose_mul, hPh] at this
  have HP : H * P = aᴴ * a := by
    rw [hH, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, hPP, sub_self, add_zero,
      Matrix.mul_assoc, hap]
  have PH : P * H = aᴴ * a := by
    rw [hH, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, add_zero,
      ← Matrix.mul_assoc, hPa]
  have comm : H⁻¹ * P = P * H⁻¹ := by
    calc H⁻¹ * P = H⁻¹ * (P * H) * H⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hr, Matrix.mul_one]
      _ = H⁻¹ * (H * P) * H⁻¹ := by rw [PH, HP]
      _ = P * H⁻¹ := by rw [← Matrix.mul_assoc, hl, Matrix.one_mul]
  refine ⟨H⁻¹ * P, H, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, PH, ← HP, ← Matrix.mul_assoc, hl, Matrix.one_mul]
  · calc aᴴ * a * (H⁻¹ * P) = H * (P * H⁻¹) * P := by
          rw [← HP]; simp only [Matrix.mul_assoc]
      _ = H * H⁻¹ * (P * P) := by rw [← comm]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hr, Matrix.one_mul, hPP]
  · rw [Matrix.mul_assoc, hPP]
end GlobalTheory.CompanionTheory.EichlerTransf
