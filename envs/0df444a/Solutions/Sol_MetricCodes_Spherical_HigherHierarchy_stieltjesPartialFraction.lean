-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.stieltjesPartialFraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/d99563b3-6eca-4849-b467-7decd98dc713

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_quadratic_injective
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lagrangeDenominator_eq_prod_erase
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stabilizerPolynomial_monic
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stabilizerPolynomial_natDegree
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stabilizerPolynomial_eval
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_ambient_quadratic_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_polynomial_partialFraction

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory
open scoped BigOperators Interval
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    (∏ i : Fin r, (t + quadraticCoordinate (b i))) /
        (∏ i : Fin (r + 1), (t + quadraticCoordinate (a i))) =
      ∑ i : Fin (r + 1),
        lagrangeWeight a b i / (t + quadraticCoordinate (a i)) := by
  classical
  let P := stabilizerPolynomial b
  have hdegree :
      P.degree < (Finset.univ : Finset (Fin (r + 1))).card := by
    rw [Polynomial.degree_eq_natDegree
      (stabilizerPolynomial_monic b).ne_zero,
      stabilizerPolynomial_natDegree]
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one]
    exact_mod_cast Nat.lt_succ_self r
  have hraw := polynomial_partialFraction h.quadratic_injective P hdegree
    (z := -t) (fun i => by
      have hnode := h.ambient_quadratic_nonneg i
      linarith)
  have hrewrite :
      (∏ i : Fin r, (-t - quadraticCoordinate (b i))) /
          (∏ i : Fin (r + 1), (-t - quadraticCoordinate (a i))) =
        ∑ i : Fin (r + 1),
          lagrangeWeight a b i / (-t - quadraticCoordinate (a i)) := by
    convert hraw using 1
    · simp [P, stabilizerPolynomial, Polynomial.eval_prod]
    · apply Finset.sum_congr rfl
      intro i _
      rw [stabilizerPolynomial_eval,
        ← lagrangeDenominator_eq_prod_erase]
      rfl
  have hneg (u : ℝ) : -t - u = -(t + u) := by ring
  simp_rw [hneg] at hrewrite
  rw [Finset.prod_neg, Finset.prod_neg] at hrewrite
  simp only [Finset.card_univ, Fintype.card_fin] at hrewrite
  have hsign : (-1 : ℝ) ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
  have hden :
      (∏ i : Fin (r + 1),
        (t + quadraticCoordinate (a i))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hnode := h.ambient_quadratic_nonneg i
    exact ne_of_gt (by linarith)
  have hleft :
      ((-1 : ℝ) ^ r * (∏ i : Fin r,
          (t + quadraticCoordinate (b i)))) /
        ((-1 : ℝ) ^ (r + 1) *
          (∏ i : Fin (r + 1),
            (t + quadraticCoordinate (a i)))) =
        -((∏ i : Fin r, (t + quadraticCoordinate (b i))) /
          (∏ i : Fin (r + 1), (t + quadraticCoordinate (a i)))) := by
    rw [pow_succ]
    field_simp [hsign, hden]
  rw [hleft] at hrewrite
  simpa only [div_neg, Finset.sum_neg_distrib, neg_inj] using hrewrite
end MetricCodes.Spherical.HigherHierarchy
