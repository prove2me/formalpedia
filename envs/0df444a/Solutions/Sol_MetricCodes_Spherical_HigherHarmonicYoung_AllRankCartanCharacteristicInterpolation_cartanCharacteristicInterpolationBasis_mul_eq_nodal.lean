-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation.cartanCharacteristicInterpolationBasis_mul_eq_nodal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/0a1c8ad0-49bc-4497-a627-727b4307de90

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℝ) (i : ι) :
    (Polynomial.X - Polynomial.C (nodes i)) *
        Lagrange.basis Finset.univ nodes i =
      Polynomial.C (Lagrange.nodalWeight Finset.univ nodes i) *
        Lagrange.nodal Finset.univ nodes := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ i),
    ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ i),
    Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ i)]
  ring
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
