-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCouplingNonzero.polynomial_eigenvector_eq_zero_of_annihilating_eval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/ca50e522-b450-4fa8-8af3-85ff5c881ed4

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
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCouplingNonzero
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCouplingNonzero
theorem _root_.solution
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V) (P : Polynomial ℝ)
    (d : ℝ) (v : V)
    (heigen : T v = d • v)
    (hchar : Polynomial.aeval T P v = 0)
    (heval : P.eval d ≠ 0) : v = 0 := by
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul heigen] at hchar
  exact (smul_eq_zero.mp hchar).resolve_left heval
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCouplingNonzero
