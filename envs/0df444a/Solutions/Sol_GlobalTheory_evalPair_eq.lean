-- Prove2me | solution 1 for GlobalTheory.evalPair_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:42.704528+00:00
-- url     : https://prove2.me/submissions/a22c7707-fddb-442f-896f-b46a6084d17a

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsConnectedPrincipalOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {d : ℕ} (z : (Fin d → ℂ) × ℂ) (r : Polynomial (MvPolynomial (Fin d) ℂ)) :
    evalPair z r = (r.map (MvPolynomial.eval z.1)).eval z.2 := by
  simp [evalPair, Polynomial.eval_map]
end GlobalTheory
