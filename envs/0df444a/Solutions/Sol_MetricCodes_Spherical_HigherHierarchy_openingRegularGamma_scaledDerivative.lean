-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.openingRegularGamma_scaledDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/889e8d86-1fa7-4470-bb57-fd09ee079d01

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ScaledOpeningDerivative_finset_sum
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_openingAmbient_scaledDerivative
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lagrangeWeight_opening_scaledDerivative

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
    (η : ℝ) :
    ScaledOpeningDerivative η
      (openingRegularGamma a b η) (openingRegularGamma a b 1) := by
  unfold openingRegularGamma
  simpa only [one_mul] using
    (ScaledOpeningDerivative.finset_sum Finset.univ fun i _ =>
    (lagrangeWeight_opening_scaledDerivative h hzero η i.castSucc).mul
      ((openingAmbient_scaledDerivative a η i.castSucc).spectralAtom
        (by simpa [openingAmbient_zero hzero] using
          (h.stabilizer_pos i).trans (h.2 i).1)))
end MetricCodes.Spherical.HigherHierarchy
