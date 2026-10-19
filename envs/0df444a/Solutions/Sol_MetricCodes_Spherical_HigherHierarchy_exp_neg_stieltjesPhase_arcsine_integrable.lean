-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exp_neg_stieltjesPhase_arcsine_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/764cad2b-d405-40ed-9383-a2151df8e8ab

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exp_neg_stieltjesPhase_integrable
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
    (h : Interlacing a b) :
    Integrable (fun t : ℝ => Real.exp (-stieltjesPhase a b t))
      Entropy.arcsineMeasure :=
  exp_neg_stieltjesPhase_integrable h Entropy.arcsineMeasure
    arcsineMeasure_ae_positive
end MetricCodes.Spherical.HigherHierarchy
