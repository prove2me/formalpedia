-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.stieltjesPhase_integrable_of_logAtoms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/31705ac4-acc7-4723-9309-726637d61184

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhase_eq_logAtom_sum

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
    (h : Interlacing a b)
    (μ : Measure ℝ)
    (hpositive : ∀ᵐ t ∂μ, 0 < t)
    (ha : ∀ i : Fin (r + 1),
      Integrable (stieltjesLogAtom (quadraticCoordinate (a i))) μ)
    (hb : ∀ i : Fin r,
      Integrable (stieltjesLogAtom (quadraticCoordinate (b i))) μ) :
    Integrable (stieltjesPhase a b) μ := by
  apply ((integrable_finsetSum _ (fun i _ => ha i)).sub
    (integrable_finsetSum _ (fun i _ => hb i))).congr
  filter_upwards [hpositive] with t ht
  exact (stieltjesPhase_eq_logAtom_sum h ht).symm
end MetricCodes.Spherical.HigherHierarchy
