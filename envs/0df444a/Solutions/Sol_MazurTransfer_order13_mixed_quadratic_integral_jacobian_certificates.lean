-- Prove2me | solution 1 for MazurTransfer.order13_mixed_quadratic_integral_jacobian_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T02:17:55.930335+00:00
-- url     : https://prove2.me/submissions/447dcd0d-c685-4bab-96a6-1403da0d210c

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: explicit integral Jacobian certificates for the two mixed
quadratic charts proposed at two. Named downstream consumer: genuine
smoothness of their coordinate algebras over the localization of Z at two.
-/
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalPolynomialsAndJacobianCoefficientData20261019
noncomputable section
open Polynomial MazurTransfer.Order13MixedQuadraticJacobianCertificates
universe u
namespace MazurTransfer.Order13MixedQuadraticIntegralJacobianProofHelpers20261019
variable (R : Type u) [CommRing R]
theorem ordinary_jacobian_certificate (x y : R)
    (hrel : y ^ 2 + (x ^ 3 + x ^ 2 + 1) * y - (x * (x + 1)) = 0) :
    (ordinaryB0 R x + ordinaryB1 R x * y) * ((3 * x ^ 2 + 2 * x) * y - (2 * x + 1)) +
      (ordinaryC0 R x + ordinaryC1 R x * y) * (2 * y + (x ^ 3 + x ^ 2 + 1)) = 117 := by
  have hid : (ordinaryB0 R x + ordinaryB1 R x * y) * ((3 * x ^ 2 + 2 * x) * y - (2 * x + 1)) +
      (ordinaryC0 R x + ordinaryC1 R x * y) * (2 * y + (x ^ 3 + x ^ 2 + 1)) =
      117 + (ordinaryB1 R x * (3 * x ^ 2 + 2 * x) + 2 * ordinaryC1 R x) *
        (y ^ 2 + (x ^ 3 + x ^ 2 + 1) * y - (x * (x + 1))) := by
    dsimp [ordinaryB0, ordinaryB1, ordinaryC0, ordinaryC1]
    ring
  rw [hid, hrel, mul_zero, add_zero]

theorem reciprocal_jacobian_certificate (x y : R)
    (hrel : y ^ 2 + (1 + x + x ^ 3) * y - (x ^ 4 + x ^ 5) = 0) :
    (reciprocalB0 R x + reciprocalB1 R x * y) * ((1 + 3 * x ^ 2) * y - (4 * x ^ 3 + 5 * x ^ 4)) +
      (reciprocalC0 R x + reciprocalC1 R x * y) * (2 * y + (1 + x + x ^ 3)) = 39 := by
  have hid : (reciprocalB0 R x + reciprocalB1 R x * y) * ((1 + 3 * x ^ 2) * y - (4 * x ^ 3 + 5 * x ^ 4)) +
      (reciprocalC0 R x + reciprocalC1 R x * y) * (2 * y + (1 + x + x ^ 3)) =
      39 + (reciprocalB1 R x * (1 + 3 * x ^ 2) + 2 * reciprocalC1 R x) *
        (y ^ 2 + (1 + x + x ^ 3) * y - (x ^ 4 + x ^ 5)) := by
    dsimp [reciprocalB0, reciprocalB1, reciprocalC0, reciprocalC1]
    ring
  rw [hid, hrel, mul_zero, add_zero]

end MazurTransfer.Order13MixedQuadraticIntegralJacobianProofHelpers20261019
theorem solution :
    (∀ (R : Type u) [CommRing R] (x y : R)
    (hrel : y ^ 2 + (x ^ 3 + x ^ 2 + 1) * y - (x * (x + 1)) = 0) ,
    (ordinaryB0 R x + ordinaryB1 R x * y) * ((3 * x ^ 2 + 2 * x) * y - (2 * x + 1)) +
      (ordinaryC0 R x + ordinaryC1 R x * y) * (2 * y + (x ^ 3 + x ^ 2 + 1)) = 117) ∧
    (∀ (R : Type u) [CommRing R] (x y : R)
    (hrel : y ^ 2 + (1 + x + x ^ 3) * y - (x ^ 4 + x ^ 5) = 0) ,
    (reciprocalB0 R x + reciprocalB1 R x * y) * ((1 + 3 * x ^ 2) * y - (4 * x ^ 3 + 5 * x ^ 4)) +
      (reciprocalC0 R x + reciprocalC1 R x * y) * (2 * y + (1 + x + x ^ 3)) = 39) := by
  exact ⟨MazurTransfer.Order13MixedQuadraticIntegralJacobianProofHelpers20261019.ordinary_jacobian_certificate,MazurTransfer.Order13MixedQuadraticIntegralJacobianProofHelpers20261019.reciprocal_jacobian_certificate⟩
#print axioms solution
