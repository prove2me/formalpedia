-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.stieltjesPhase_comparison_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/c5019a87-077e-42b6-a272-87b18bb7e0ac

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparison_log_integrable_of_logMoment
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_ambient_quadratic_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_stabilizer_quadratic_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesLogAtom_integrable_of_log
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhase_integrable_of_logAtoms
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_comparisonMeasure_ae_positive_le_one

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
    (hlogMoment :
      (∫ t : ℝ, Real.log t ∂Entropy.comparisonMeasure) = -2) :
    Integrable (stieltjesPhase a b) Entropy.comparisonMeasure := by
  have hlog := Entropy.comparison_log_integrable_of_logMoment hlogMoment
  apply stieltjesPhase_integrable_of_logAtoms h
    Entropy.comparisonMeasure
    (comparisonMeasure_ae_positive_le_one.mono (fun _ h => h.1))
  · intro i
    exact stieltjesLogAtom_integrable_of_log
      Entropy.comparisonMeasure (h.ambient_quadratic_nonneg i)
      comparisonMeasure_ae_positive_le_one hlog
  · intro i
    exact stieltjesLogAtom_integrable_of_log
      Entropy.comparisonMeasure (h.stabilizer_quadratic_pos i).le
      comparisonMeasure_ae_positive_le_one hlog
end MetricCodes.Spherical.HigherHierarchy
