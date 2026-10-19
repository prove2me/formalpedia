-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.stieltjesPhase_arcsine_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/55882e44-0bc9-4f99-9c43-afc9aa16608d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_ambient_quadratic_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_quadratic_spectralAtom_identity
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_integral_exp_neg_stieltjesPhase_eq_one_sub_two_Gamma
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_arcsineMeasure_ae_positive

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (harcsine : ∀ x : ℝ, 0 ≤ x →
      (∫ t : ℝ, t / (t + x) ∂Entropy.arcsineMeasure) =
        1 - Real.sqrt (x / (x + 1 / 4))) :
    Entropy.phaseNormalizer (stieltjesPhase a b) =
      1 - 2 * Gamma a b := by
  unfold Entropy.phaseNormalizer
  apply integral_exp_neg_stieltjesPhase_eq_one_sub_two_Gamma h
    Entropy.arcsineMeasure arcsineMeasure_ae_positive
  intro i
  rw [harcsine (quadraticCoordinate (a i))
    (h.ambient_quadratic_nonneg i),
    quadratic_spectralAtom_identity (h.ambient_nonneg i)]
end MetricCodes.Spherical.HigherHierarchy
