-- Prove2me | solution 1 for MazurTransfer.order13_mixed_quadratic_unit_and_smoothness_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T02:21:47.956209+00:00
-- url     : https://prove2.me/submissions/4732636a-9ca3-4565-a7d9-a9d0769fb613

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal mixed quadratic ordinary and reciprocal
coordinate rings are smooth when their odd Jacobian constants are units.
Named downstream consumer: actual affine chart schemes over Z localized at two.
-/
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalPolynomialsAndJacobianCoefficientData20261019
import Definitions.Def_MazurTransfer_MixedQuadraticOriginalCoordinateEquationAndJacobianData20261019
import Theorems.Thm_MazurTransfer_order13_mixed_quadratic_integral_jacobian_certificates
import Theorems.Thm_MazurTransfer_mixed_quadratic_coordinate_smooth
noncomputable section
open Polynomial MazurTransfer.MixedQuadraticCoordinateJacobian MazurTransfer.Order13MixedQuadraticJacobianCertificates
universe u v
namespace MazurTransfer.Order13MixedQuadraticSmoothnessProofHelpers20261019
namespace Generic
variable (R : Type u) [CommRing R]
theorem root_relation (h f : Polynomial R) :
    AdjoinRoot.root (equation R h f) ^ 2 +
      AdjoinRoot.of (equation R h f) h * AdjoinRoot.root (equation R h f) -
      AdjoinRoot.of (equation R h f) f = 0 := by
  have ht := AdjoinRoot.eval₂_root (equation R h f)
  change eval₂ (AdjoinRoot.of (equation R h f)) (AdjoinRoot.root (equation R h f))
    (X ^ 2 + C h * X - C f) = 0 at ht
  simpa only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C] using ht

end Generic
namespace Evaluations
variable (R : Type u) [CommRing R] {A : Type v} [CommRing A] (ι : Polynomial R →+* A)

theorem map_ordinaryH : ι (ordinaryH R) = ι X ^ 3 + ι X ^ 2 + 1 := by
  change ι (X ^ 3 + X ^ 2 + 1) = _
  rw [map_add, map_add, map_pow, map_pow, map_one]
theorem map_ordinaryF : ι (ordinaryF R) = ι X * (ι X + 1) := by
  change ι (X * (X + 1)) = _
  rw [map_mul, map_add, map_one]
theorem map_reciprocalH : ι (reciprocalH R) = 1 + ι X + ι X ^ 3 := by
  change ι (1 + X + X ^ 3) = _
  rw [map_add, map_add, map_one, map_pow]
theorem map_reciprocalF : ι (reciprocalF R) = ι X ^ 4 + ι X ^ 5 := by
  change ι (X ^ 4 + X ^ 5) = _
  rw [map_add, map_pow, map_pow]

theorem ordinaryH_derivative : (ordinaryH R).derivative = 3 * X ^ 2 + 2 * X := by
  simp only [ordinaryH, derivative_add, derivative_pow, derivative_X, derivative_one,
    mul_one, add_zero]
  norm_num
  simp only [Polynomial.C_ofNat] <;> ring
theorem ordinaryF_derivative : (ordinaryF R).derivative = 2 * X + 1 := by
  simp only [ordinaryF, derivative_mul, derivative_add, derivative_X, derivative_one,
    mul_one, one_mul, add_zero]
  ring
theorem reciprocalH_derivative : (reciprocalH R).derivative = 1 + 3 * X ^ 2 := by
  simp only [reciprocalH, derivative_add, derivative_pow, derivative_X, derivative_one,
    mul_one, zero_add]
  norm_num
  simp only [Polynomial.C_ofNat] <;> ring
theorem reciprocalF_derivative : (reciprocalF R).derivative = 4 * X ^ 3 + 5 * X ^ 4 := by
  simp only [reciprocalF, derivative_add, derivative_pow, derivative_X, mul_one]
  norm_num
  simp only [Polynomial.C_ofNat] <;> ring

theorem map_ordinaryH_derivative : ι (ordinaryH R).derivative = 3 * ι X ^ 2 + 2 * ι X := by
  rw [ordinaryH_derivative, map_add, map_mul, map_mul, map_pow, map_ofNat, map_ofNat]
theorem map_ordinaryF_derivative : ι (ordinaryF R).derivative = 2 * ι X + 1 := by
  rw [ordinaryF_derivative, map_add, map_mul, map_ofNat, map_one]
theorem map_reciprocalH_derivative : ι (reciprocalH R).derivative = 1 + 3 * ι X ^ 2 := by
  rw [reciprocalH_derivative, map_add, map_one, map_mul, map_pow, map_ofNat]
theorem map_reciprocalF_derivative : ι (reciprocalF R).derivative = 4 * ι X ^ 3 + 5 * ι X ^ 4 := by
  rw [reciprocalF_derivative, map_add, map_mul, map_mul, map_pow, map_pow, map_ofNat, map_ofNat]

end Evaluations
namespace Actual
open Generic Evaluations
variable (R : Type u) [CommRing R]
theorem ordinary_jacobian_unit (hu : IsUnit (117 : R)) :
    ∃ a b : CoordinateRing R (ordinaryH R) (ordinaryF R),
      a * partialX R (ordinaryH R) (ordinaryF R) + b * partialY R (ordinaryH R) (ordinaryF R) = 1 := by
  let q := equation R (ordinaryH R) (ordinaryF R)
  let x : CoordinateRing R (ordinaryH R) (ordinaryF R) := AdjoinRoot.of q X
  let y : CoordinateRing R (ordinaryH R) (ordinaryF R) := AdjoinRoot.root q
  have hrel : y ^ 2 + (x ^ 3 + x ^ 2 + 1) * y - (x * (x + 1)) = 0 := by
    have ht := root_relation R (ordinaryH R) (ordinaryF R)
    change y ^ 2 + AdjoinRoot.of q (ordinaryH R) * y - AdjoinRoot.of q (ordinaryF R) = 0 at ht
    rw [map_ordinaryH R (AdjoinRoot.of q), map_ordinaryF R (AdjoinRoot.of q)] at ht
    exact ht
  have hjx : partialX R (ordinaryH R) (ordinaryF R) = (3 * x ^ 2 + 2 * x) * y - (2 * x + 1) := by
    change AdjoinRoot.of q (ordinaryH R).derivative * y - AdjoinRoot.of q (ordinaryF R).derivative = _
    rw [map_ordinaryH_derivative R (AdjoinRoot.of q), map_ordinaryF_derivative R (AdjoinRoot.of q)]
  have hjy : partialY R (ordinaryH R) (ordinaryF R) = 2 * y + (x ^ 3 + x ^ 2 + 1) := by
    change 2 * y + AdjoinRoot.of q (ordinaryH R) = _
    rw [map_ordinaryH R (AdjoinRoot.of q)]
  let a : CoordinateRing R (ordinaryH R) (ordinaryF R) := ordinaryB0 _ x + ordinaryB1 _ x * y
  let b : CoordinateRing R (ordinaryH R) (ordinaryF R) := ordinaryC0 _ x + ordinaryC1 _ x * y
  have hcert : a * partialX R (ordinaryH R) (ordinaryF R) + b * partialY R (ordinaryH R) (ordinaryF R) = 117 := by
    rw [hjx, hjy]
    exact (MazurTransfer.order13_mixed_quadratic_integral_jacobian_certificates).1 _ x y hrel
  have hua : IsUnit (117 : CoordinateRing R (ordinaryH R) (ordinaryF R)) := by
    simpa only [_root_.map_ofNat] using hu.map (algebraMap R (CoordinateRing R (ordinaryH R) (ordinaryF R)))
  obtain ⟨v, hv⟩ := hua
  have hinv : (↑(v⁻¹) : CoordinateRing R (ordinaryH R) (ordinaryF R)) * 117 = 1 := by rw [← hv]; simp
  refine ⟨↑(v⁻¹) * a, ↑(v⁻¹) * b, ?_⟩
  calc
    _ = ↑(v⁻¹) * (a * partialX R (ordinaryH R) (ordinaryF R) + b * partialY R (ordinaryH R) (ordinaryF R)) := by ring
    _ = 1 := by rw [hcert, hinv]

theorem ordinary_smooth (hu : IsUnit (117 : R)) :
    Algebra.Smooth R (CoordinateRing R (ordinaryH R) (ordinaryF R)) :=
  MazurTransfer.mixed_quadratic_coordinate_smooth R (ordinaryH R) (ordinaryF R) (ordinary_jacobian_unit R hu)

theorem reciprocal_jacobian_unit (hu : IsUnit (39 : R)) :
    ∃ a b : CoordinateRing R (reciprocalH R) (reciprocalF R),
      a * partialX R (reciprocalH R) (reciprocalF R) + b * partialY R (reciprocalH R) (reciprocalF R) = 1 := by
  let q := equation R (reciprocalH R) (reciprocalF R)
  let x : CoordinateRing R (reciprocalH R) (reciprocalF R) := AdjoinRoot.of q X
  let y : CoordinateRing R (reciprocalH R) (reciprocalF R) := AdjoinRoot.root q
  have hrel : y ^ 2 + (1 + x + x ^ 3) * y - (x ^ 4 + x ^ 5) = 0 := by
    have ht := root_relation R (reciprocalH R) (reciprocalF R)
    change y ^ 2 + AdjoinRoot.of q (reciprocalH R) * y - AdjoinRoot.of q (reciprocalF R) = 0 at ht
    rw [map_reciprocalH R (AdjoinRoot.of q), map_reciprocalF R (AdjoinRoot.of q)] at ht
    exact ht
  have hjx : partialX R (reciprocalH R) (reciprocalF R) = (1 + 3 * x ^ 2) * y - (4 * x ^ 3 + 5 * x ^ 4) := by
    change AdjoinRoot.of q (reciprocalH R).derivative * y - AdjoinRoot.of q (reciprocalF R).derivative = _
    rw [map_reciprocalH_derivative R (AdjoinRoot.of q), map_reciprocalF_derivative R (AdjoinRoot.of q)]
  have hjy : partialY R (reciprocalH R) (reciprocalF R) = 2 * y + (1 + x + x ^ 3) := by
    change 2 * y + AdjoinRoot.of q (reciprocalH R) = _
    rw [map_reciprocalH R (AdjoinRoot.of q)]
  let a : CoordinateRing R (reciprocalH R) (reciprocalF R) := reciprocalB0 _ x + reciprocalB1 _ x * y
  let b : CoordinateRing R (reciprocalH R) (reciprocalF R) := reciprocalC0 _ x + reciprocalC1 _ x * y
  have hcert : a * partialX R (reciprocalH R) (reciprocalF R) + b * partialY R (reciprocalH R) (reciprocalF R) = 39 := by
    rw [hjx, hjy]
    exact (MazurTransfer.order13_mixed_quadratic_integral_jacobian_certificates).2 _ x y hrel
  have hua : IsUnit (39 : CoordinateRing R (reciprocalH R) (reciprocalF R)) := by
    simpa only [_root_.map_ofNat] using hu.map (algebraMap R (CoordinateRing R (reciprocalH R) (reciprocalF R)))
  obtain ⟨v, hv⟩ := hua
  have hinv : (↑(v⁻¹) : CoordinateRing R (reciprocalH R) (reciprocalF R)) * 39 = 1 := by rw [← hv]; simp
  refine ⟨↑(v⁻¹) * a, ↑(v⁻¹) * b, ?_⟩
  calc
    _ = ↑(v⁻¹) * (a * partialX R (reciprocalH R) (reciprocalF R) + b * partialY R (reciprocalH R) (reciprocalF R)) := by ring
    _ = 1 := by rw [hcert, hinv]

theorem reciprocal_smooth (hu : IsUnit (39 : R)) :
    Algebra.Smooth R (CoordinateRing R (reciprocalH R) (reciprocalF R)) :=
  MazurTransfer.mixed_quadratic_coordinate_smooth R (reciprocalH R) (reciprocalF R) (reciprocal_jacobian_unit R hu)

end Actual
end MazurTransfer.Order13MixedQuadraticSmoothnessProofHelpers20261019
theorem solution :
    (∀ (R : Type u) [CommRing R] (hu : IsUnit (117 : R)) ,
    ∃ a b : CoordinateRing R (ordinaryH R) (ordinaryF R),
      a * partialX R (ordinaryH R) (ordinaryF R) + b * partialY R (ordinaryH R) (ordinaryF R) = 1) ∧
    (∀ (R : Type u) [CommRing R] (hu : IsUnit (117 : R)) ,
    Algebra.Smooth R (CoordinateRing R (ordinaryH R) (ordinaryF R))) ∧
    (∀ (R : Type u) [CommRing R] (hu : IsUnit (39 : R)) ,
    ∃ a b : CoordinateRing R (reciprocalH R) (reciprocalF R),
      a * partialX R (reciprocalH R) (reciprocalF R) + b * partialY R (reciprocalH R) (reciprocalF R) = 1) ∧
    (∀ (R : Type u) [CommRing R] (hu : IsUnit (39 : R)) ,
    Algebra.Smooth R (CoordinateRing R (reciprocalH R) (reciprocalF R))) := by
  exact ⟨MazurTransfer.Order13MixedQuadraticSmoothnessProofHelpers20261019.Actual.ordinary_jacobian_unit,MazurTransfer.Order13MixedQuadraticSmoothnessProofHelpers20261019.Actual.ordinary_smooth,MazurTransfer.Order13MixedQuadraticSmoothnessProofHelpers20261019.Actual.reciprocal_jacobian_unit,MazurTransfer.Order13MixedQuadraticSmoothnessProofHelpers20261019.Actual.reciprocal_smooth⟩
#print axioms solution
