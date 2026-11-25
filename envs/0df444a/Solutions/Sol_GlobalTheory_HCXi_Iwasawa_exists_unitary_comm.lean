-- Prove2me | solution 1 for GlobalTheory.HCXi.Iwasawa.exists_unitary_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:06:38.942889+00:00
-- url     : https://prove2.me/submissions/fbf515d1-50a0-4666-8480-4322bd483e0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsUnitaryOfGramEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsQr
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitive
import Theorems.Thm_GlobalTheory_UnitaryExtension_exists_unitary_of_gram_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi
namespace GlobalTheory.HCXi
namespace Iwasawa
theorem _root_.solution {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (A B : Matrix (Fin n) (Fin m) ℂ) (h1 : Aᴴ * A = Bᴴ * B) (h2 : Aᴴ * H * A = Bᴴ * H * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * H = H * U ∧ U * A = B := by
  set P : Matrix (Fin n) (Fin n) ℂ := (2⁻¹ : ℂ) • (1 + H) with hP
  have hPh : Pᴴ = P := by
    simp [hP, conjTranspose_smul, conjTranspose_add, hH]
  have hPP : P * P = P := by
    simp only [hP, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, one_mul, mul_one, hHH]
    module
  have hHP : H = (2 : ℂ) • P - 1 := by
    simp only [hP]
    module
  have hG : Aᴴ * P * A = Bᴴ * P * B := by
    simp only [hP, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1, h2]
  clear_value P
  have hQh : (1 - P)ᴴ = 1 - P := by simp [hPh]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    simp only [mul_sub, sub_mul, one_mul, mul_one, hPP, sub_self, sub_zero]
  have hG' : Aᴴ * (1 - P) * A = Bᴴ * (1 - P) * B := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, hG]
  have key : ∀ E : Matrix (Fin n) (Fin n) ℂ, Eᴴ = E → E * E = E → Aᴴ * E * A = Bᴴ * E * B →
      ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * E = E * U ∧ U * (1 - E) = 1 - E ∧ U * (E * A) = E * B := by
    intro E hE hEE hg
    have e : ∀ C : Matrix (Fin n) (Fin m) ℂ, (E * C)ᴴ * (E * C) = Cᴴ * E * C := by
      intro C
      rw [conjTranspose_mul, hE, Matrix.mul_assoc, ← Matrix.mul_assoc E E, hEE, Matrix.mul_assoc]
    refine GlobalTheory.UnitaryExtension.exists_unitary_of_gram_eq n m E (E * A) (E * B) hE hEE ?_ ?_ ?_
    · rw [← Matrix.mul_assoc, hEE]
    · rw [← Matrix.mul_assoc, hEE]
    · rw [e, e, hg]
  obtain ⟨U, hU1, hU2, hU3, hU4⟩ := key P hPh hPP hG
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ := key (1 - P) hQh hQQ hG'
  rw [sub_sub_cancel] at hV3
  have hV5 : V * P = P * V := by
    have := hV2
    simp only [mul_sub, sub_mul, one_mul, mul_one] at this
    exact sub_right_injective this
  refine ⟨U * V, ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, hV1]
  · have : U * V * P = P * (U * V) := by
      rw [mul_assoc, hV5, ← mul_assoc, hU2, mul_assoc]
    rw [hHP]
    simp only [mul_sub, sub_mul, one_mul, mul_one, mul_smul_comm, smul_mul_assoc, this]
  · have hA : A = P * A + (1 - P) * A := by
      rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    have hB : B = P * B + (1 - P) * B := by
      rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    calc U * V * A = U * (V * (P * A + (1 - P) * A)) := by rw [← hA, Matrix.mul_assoc]
      _ = U * (P * A + (1 - P) * B) := by
        rw [Matrix.mul_add, hV4, ← Matrix.mul_assoc V P, hV3]
      _ = P * B + (1 - P) * B := by
        rw [Matrix.mul_add, hU4, ← Matrix.mul_assoc U (1 - P), hU3]
      _ = B := hB.symm
end Iwasawa
end GlobalTheory.HCXi
