-- Prove2me | solution 1 for GlobalTheory.FormalCalc.pderiv_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:50.788868+00:00
-- url     : https://prove2.me/submissions/adef7ea3-6d2b-4ec5-a136-47953700643a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Finsupp
variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
namespace GlobalTheory.FormalCalc
theorem _root_.solution (i j : σ) (f : MvPowerSeries σ R) :
    pderiv R i (pderiv R j f) = pderiv R j (pderiv R i f) := by
  classical
  by_cases h : i = j
  · rw [h]
  ext d
  simp only [coeff_pderiv, Finsupp.add_apply, single_eq_of_ne h, single_eq_of_ne (Ne.symm h),
    add_zero]
  rw [add_right_comm]
  ring
end GlobalTheory.FormalCalc
