-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Interlacing.sum_lagrangeWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/c8bc2607-c626-45a8-9aa0-c9e3c4489913

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_quadratic_injective
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lagrangeDenominator_eq_prod_erase
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stabilizerPolynomial_monic
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stabilizerPolynomial_natDegree
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stabilizerPolynomial_eval

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
namespace Interlacing
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    (∑ ℓ : Fin (r + 1), lagrangeWeight a b ℓ) = 1 := by
  classical
  let P : Polynomial ℝ := stabilizerPolynomial b
  have hmonic : P.Monic := stabilizerPolynomial_monic b
  have hdegree : P.natDegree = r := stabilizerPolynomial_natDegree b
  have hdegree' :
      P.degree < (Finset.univ : Finset (Fin (r + 1))).card := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdegree]
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    exact_mod_cast Nat.lt_succ_self r
  have hlagrange := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin (r + 1))))
    (v := fun ℓ : Fin (r + 1) => quadraticCoordinate (a ℓ))
    (P := P) h.quadratic_injective.injOn hdegree'
  have hcoeff : P.coeff r = 1 := by
    simpa [hdegree] using hmonic.coeff_natDegree
  rw [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel,
    hcoeff] at hlagrange
  symm
  calc
    1 = ∑ ℓ : Fin (r + 1),
        P.eval (quadraticCoordinate (a ℓ)) /
          ∏ j ∈ Finset.univ.erase ℓ,
            (quadraticCoordinate (a ℓ) - quadraticCoordinate (a j)) := by
          simpa using hlagrange
    _ = ∑ ℓ : Fin (r + 1), lagrangeWeight a b ℓ := by
          apply Finset.sum_congr rfl
          intro ℓ _
          rw [lagrangeWeight, lagrangeDenominator_eq_prod_erase,
            ← stabilizerPolynomial_eval]
end Interlacing
end MetricCodes.Spherical.HigherHierarchy
