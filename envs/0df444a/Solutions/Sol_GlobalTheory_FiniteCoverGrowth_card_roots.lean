-- Prove2me | solution 1 for GlobalTheory.FiniteCoverGrowth.card_roots
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:56.505343+00:00
-- url     : https://prove2.me/submissions/7395d7b3-46f6-4fdb-99e9-08f4bb22004f

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IntegralAndRationalOfPolynomialGrowth
import Theorems.Thm_GlobalTheory_FiniteCoverGrowth_eq_nodal

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
open GlobalTheory GlobalTheory.FiniteCoverGrowth
namespace GlobalTheory.FiniteCoverGrowth
theorem _root_.solution {P : Polynomial ℂ} (hm : P.Monic) (hs : P.Separable) :
    P.roots.toFinset.card = P.natDegree := by
  conv_rhs => rw [eq_nodal hm hs, Lagrange.natDegree_nodal]
end GlobalTheory.FiniteCoverGrowth
