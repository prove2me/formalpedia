-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.lagrangeWeight_eq_residue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/d9a729e7-8042-4435-8e44-d19a68d3f0f6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeDenominator_ne_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stabilizerPolynomial_eval
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_ambient_stabilizer_interlacing
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_quadraticCoordinate_ambient
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_normalizedDerivative_eq_stabilizerPolynomial
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_polePolynomial_derivative_eval_pole_eq_lagrangeDenominator

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R)
    (r : ℕ) (ℓ : Fin (r + 1)) :
    MetricCodes.Spherical.HigherHierarchy.lagrangeWeight
      (ambient R r) (stabilizer R r) ℓ = residue (r + 1) := by
  have hden := (ambient_stabilizer_interlacing hR r).lagrangeDenominator_ne_zero ℓ
  have heq := congrArg (Polynomial.eval (pole R (r + 1) ℓ.val))
    (normalizedDerivative_eq_stabilizerPolynomial hR r)
  simp only [normalizedDerivative, Polynomial.eval_mul,
    Polynomial.eval_C] at heq
  rw [polePolynomial_derivative_eval_pole_eq_lagrangeDenominator
    hR r ℓ] at heq
  have hnum :
      MetricCodes.Spherical.HigherHierarchy.lagrangeNumerator
        (ambient R r) (stabilizer R r) ℓ =
      MetricCodes.Spherical.HigherHierarchy.lagrangeDenominator
        (ambient R r) ℓ / ((r + 1 : ℕ) : ℝ) := by
    rw [← MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial_eval]
    rw [quadraticCoordinate_ambient hR r ℓ]
    rw [← heq]
    ring
  unfold MetricCodes.Spherical.HigherHierarchy.lagrangeWeight residue
  rw [hnum]
  field_simp
end MetricCodes.Spherical.HigherHierarchyChebyshev
