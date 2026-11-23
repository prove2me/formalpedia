-- Prove2me | solution 1 for GlobalTheory.evalPair_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:43.786495+00:00
-- url     : https://prove2.me/submissions/b60d4c85-30a7-4003-92a6-4e4124a7f22e

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
theorem _root_.solution {d : ℕ} (z : (Fin d → ℂ) × ℂ) (s : MvPolynomial (Fin d) ℂ) :
    evalPair z (Polynomial.C s) = MvPolynomial.eval z.1 s := by
  simp [evalPair]
end GlobalTheory
