-- Prove2me | solution 1 for GlobalTheory.int_bezout_derivative_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:00:10.467189+00:00
-- url     : https://prove2.me/submissions/e8eb9889-3101-450e-aaaf-134fd6c428e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLargePrimeDvdIntPolynomialEvalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepIntPolyRootModPrimeSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution (f : ℤ[X])
    (hf : (f.map (Int.castRingHom ℚ)).Separable) :
    ∃ A B : ℤ[X], ∃ N : ℤ, N ≠ 0 ∧ A * f + B * derivative f = C N := by
  obtain ⟨a, b, hab⟩ := hf
  obtain ⟨c1, hc1⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) a
  obtain ⟨c2, hc2⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors ℤ) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors ℤ) b
  refine ⟨(c2 : ℤ) • A, (c1 : ℤ) • B, (c1 : ℤ) * c2, ?_, ?_⟩
  · exact mul_ne_zero (nonZeroDivisors.coe_ne_zero c1) (nonZeroDivisors.coe_ne_zero c2)
  · apply Polynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    have e1 : A.map (Int.castRingHom ℚ) = ((c1 : ℤ) : ℚ) • a := by
      rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hc1]
      exact (Int.cast_smul_eq_zsmul ℚ _ _).symm
    have e2 : B.map (Int.castRingHom ℚ) = ((c2 : ℤ) : ℚ) • b := by
      rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hc2]
      exact (Int.cast_smul_eq_zsmul ℚ _ _).symm
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_smul, Polynomial.map_C,
      ← Polynomial.derivative_map, e1, e2]
    rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]
    calc _ = C (((c1 : ℤ) : ℚ) * ((c2 : ℤ) : ℚ)) *
            (a * map (Int.castRingHom ℚ) f + b * derivative (map (Int.castRingHom ℚ) f)) := by
          rw [C_mul]; simp only [eq_intCast]; ring
      _ = _ := by rw [hab, mul_one]; simp
end GlobalTheory
