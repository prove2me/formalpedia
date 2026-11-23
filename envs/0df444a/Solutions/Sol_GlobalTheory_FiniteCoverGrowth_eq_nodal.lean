-- Prove2me | solution 1 for GlobalTheory.FiniteCoverGrowth.eq_nodal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:40.356795+00:00
-- url     : https://prove2.me/submissions/4457f129-4442-42bd-9105-1af869d0517f

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IntegralAndRationalOfPolynomialGrowth

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
    P = Lagrange.nodal P.roots.toFinset id := by
  classical
  rw [Lagrange.nodal_eq, Finset.prod, Multiset.toFinset_val,
    (Polynomial.nodup_roots hs).dedup]
  exact (IsAlgClosed.splits P).eq_prod_roots_of_monic hm
end GlobalTheory.FiniteCoverGrowth
