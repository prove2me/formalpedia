-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement.gtStabilizerArrowheadMinor_eq_channelNumerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/6b0a7332-b803-4dc4-8a62-ad210cf86a0e

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
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000
open scoped BigOperators
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
theorem _root_.solution {r : ℕ}
    (rho : ℝ) (M : Fin r → ℝ) :
    gtStabilizerArrowheadMinor rho M =
      channelNumeratorPolynomial rho M := by
  classical
  unfold gtStabilizerArrowheadMinor Lagrange.nodal
    channelNumeratorPolynomial
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique, Fintype.prod_prod_type,
    Fintype.prod_bool]
  congr 1
  · simp [gtStabilizerArrowheadNode]
  · apply Finset.prod_congr rfl
    intro m _
    simp only [gtStabilizerArrowheadNode, map_sub, map_neg, map_add]
    ring
end MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
