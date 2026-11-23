-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.eventually_nhdsNE_zero_eval_weierstrassP_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:37.768176+00:00
-- url     : https://prove2.me/submissions/67c3248c-4563-46f2-809a-69172f2cf0e6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {Q : ℂ[X]} (hQ : Q ≠ 0) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), Q.eval (℘[L] z) ≠ 0 := by
  have hcob : Tendsto ℘[L] (𝓝[≠] 0) (Bornology.cobounded ℂ) := by
    apply tendsto_cobounded_of_meromorphicOrderAt_neg
    rw [L.order_weierstrassP 0 L.lattice.zero_mem]
    decide
  have hb : Bornology.IsBounded {w : ℂ | Q.IsRoot w} :=
    (Polynomial.finite_setOfPred_isRoot hQ).isBounded
  filter_upwards [hcob.eventually hb] with z hz
  exact hz
end GroundTheory.Global.Elliptic
