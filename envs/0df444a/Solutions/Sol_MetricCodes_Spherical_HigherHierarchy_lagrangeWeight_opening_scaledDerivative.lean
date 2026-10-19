-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.lagrangeWeight_opening_scaledDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/6bd7b6f2-6c35-40ba-bda4-a547c7f1021a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeDenominator_ne_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ScaledOpeningDerivative_finset_prod
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_openingAmbient_scaledDerivative

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0)
    (η : ℝ) (i : Fin (r + 1)) :
    ScaledOpeningDerivative η
      (fun t => lagrangeWeight (openingAmbient a (η * t) (t ^ 2)) b i)
      (fun t => lagrangeWeight (openingAmbient a t (t ^ 2)) b i) := by
  unfold lagrangeWeight lagrangeNumerator lagrangeDenominator
  have hnum : ScaledOpeningDerivative η
      (fun t => ∏ j : Fin r,
        (quadraticCoordinate (openingAmbient a (η * t) (t ^ 2) i) -
          quadraticCoordinate (b j)))
      (fun t => ∏ j : Fin r,
        (quadraticCoordinate (openingAmbient a t (t ^ 2) i) -
          quadraticCoordinate (b j))) := by
    exact ScaledOpeningDerivative.finset_prod Finset.univ fun j _ =>
      (openingAmbient_scaledDerivative a η i).quadraticCoordinate.sub
        (ScaledOpeningDerivative.const η (quadraticCoordinate (b j)))
  have hden : ScaledOpeningDerivative η
      (fun t => ∏ j : Fin r,
        (quadraticCoordinate (openingAmbient a (η * t) (t ^ 2) i) -
          quadraticCoordinate (openingAmbient a (η * t) (t ^ 2)
            (i.succAbove j))))
      (fun t => ∏ j : Fin r,
        (quadraticCoordinate (openingAmbient a t (t ^ 2) i) -
          quadraticCoordinate (openingAmbient a t (t ^ 2)
            (i.succAbove j)))) := by
    exact ScaledOpeningDerivative.finset_prod Finset.univ fun j _ =>
      (openingAmbient_scaledDerivative a η i).quadraticCoordinate.sub
        (openingAmbient_scaledDerivative a η (i.succAbove j)).quadraticCoordinate
  have hnonzero :
      (∏ j : Fin r,
        (quadraticCoordinate (openingAmbient a 0 0 i) -
          quadraticCoordinate (openingAmbient a 0 0 (i.succAbove j)))) ≠ 0 := by
    change lagrangeDenominator (openingAmbient a 0 0) i ≠ 0
    rw [openingAmbient_zero hzero]
    exact h.lagrangeDenominator_ne_zero i
  simpa using hnum.div hden (by simpa [zero_pow (by norm_num : 2 ≠ 0)] using hnonzero)
end MetricCodes.Spherical.HigherHierarchy
