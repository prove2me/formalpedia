-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.normalizedDerivative_eq_stabilizerPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/ae22f5ff-961a-41af-b344-7932b0f57dea

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stabilizerPolynomial_monic
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stabilizerPolynomial_natDegree
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_quadraticCoordinate_stabilizer
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_polePolynomial_derivative_eval_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_normalizedDerivative_monic
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_normalizedDerivative_natDegree
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_zero_nodes_injective

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution
    {R : ℝ} (hR : 0 < R) (r : ℕ) :
    normalizedDerivative R r =
      MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial
        (stabilizer R r) := by
  let P := normalizedDerivative R r
  let Q := MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial
    (stabilizer R r)
  have hP : Polynomial.IsMonicOfDegree P r :=
    ⟨normalizedDerivative_natDegree R r,
      normalizedDerivative_monic R r⟩
  have hQ : Polynomial.IsMonicOfDegree Q r :=
    ⟨MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial_natDegree
        (stabilizer R r),
      MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial_monic
        (stabilizer R r)⟩
  by_cases hr : r = 0
  · subst r
    exact (Polynomial.isMonicOfDegree_zero_iff.mp hP).trans
      (Polynomial.isMonicOfDegree_zero_iff.mp hQ).symm
  · have hdeg : (P - Q).natDegree < r := hP.natDegree_sub_lt hr hQ
    have hzero : P - Q = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
        (P - Q) (zero_nodes_injective hR r)
      · intro i
        rw [Polynomial.eval_sub]
        have hPi : P.eval (zero R (r + 1) (i.val + 1)) = 0 := by
          dsimp [P, normalizedDerivative]
          rw [Polynomial.eval_mul, Polynomial.eval_C]
          rw [polePolynomial_derivative_eval_zero hR (by omega)
            (by omega)]
          ring
        rw [hPi]
        have hQi : Q.eval (zero R (r + 1) (i.val + 1)) = 0 := by
          unfold Q MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial
          rw [Polynomial.eval_prod]
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp [quadraticCoordinate_stabilizer hR r i]
        rw [hQi]
        ring
      · simpa using hdeg
    exact sub_eq_zero.mp hzero
end MetricCodes.Spherical.HigherHierarchyChebyshev
