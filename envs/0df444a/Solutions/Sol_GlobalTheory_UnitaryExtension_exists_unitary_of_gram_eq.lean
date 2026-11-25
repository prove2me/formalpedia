-- Prove2me | solution 1 for GlobalTheory.UnitaryExtension.exists_unitary_of_gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:19:25.762511+00:00
-- url     : https://prove2.me/submissions/d9b7b044-55ae-4883-bbe8-30e27af03366

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsUnitaryOfGramEq
import Theorems.Thm_GlobalTheory_UnitaryExtension_exists_unitary_mul_eq

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
open GlobalTheory GlobalTheory.UnitaryExtension
namespace GlobalTheory.UnitaryExtension
theorem _root_.solution : ∀ (n m : ℕ) (E : Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin m) ℂ), Eᴴ = E → E * E = E → E * A = A → E * B = B → Aᴴ * A = Bᴴ * B → ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * E = E * U ∧ U * (1 - E) = 1 - E ∧ U * A = B := by
  intro n m E A B hE hEE hA hB hG
  have hP : (1 - E)ᴴ = 1 - E := by rw [conjTranspose_sub, conjTranspose_one, hE]
  have hPA : (1 - E) * A = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hA, sub_self]
  have hPB : (1 - E) * B = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hB, sub_self]
  have hAP : Aᴴ * (1 - E) = 0 := by
    rw [← hP, ← conjTranspose_mul, hPA, conjTranspose_zero]
  have hBP : Bᴴ * (1 - E) = 0 := by
    rw [← hP, ← conjTranspose_mul, hPB, conjTranspose_zero]
  obtain ⟨U, hU, hUA⟩ := exists_unitary_mul_eq (Matrix.fromCols A (1 - E))
    (Matrix.fromCols B (1 - E)) (by
      rw [conjTranspose_fromCols_eq_fromRows_conjTranspose,
        conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols,
        fromRows_mul_fromCols, hP, hG, hPA, hPB, hAP, hBP])
  rw [mul_fromCols, fromCols_ext_iff] at hUA
  obtain ⟨h1, h2⟩ := hUA
  refine ⟨U, hU, ?_, h2, h1⟩
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have h3 : (1 - E) * Uᴴ = 1 - E := by
    have := congrArg conjTranspose h2
    rwa [conjTranspose_mul, hP] at this
  have h4 : (1 - E) * U = 1 - E := by
    calc (1 - E) * U = (1 - E) * Uᴴ * U := by rw [h3]
      _ = 1 - E := by rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  have h5 : U * (1 - E) = (1 - E) * U := by rw [h2, h4]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul] at h5
  exact sub_right_injective h5
end GlobalTheory.UnitaryExtension
