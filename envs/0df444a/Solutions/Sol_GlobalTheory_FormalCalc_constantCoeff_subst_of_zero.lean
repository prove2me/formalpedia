-- Prove2me | solution 1 for GlobalTheory.FormalCalc.constantCoeff_subst_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:44.236491+00:00
-- url     : https://prove2.me/submissions/31efedae-b72b-46a4-9dd4-b17b44e53ed2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_C__c5547c7a475b

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
theorem _root_.solution {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = algebraMap R S (constantCoeff f) := by
  have h : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by simp
  have h' : constantCoeff (subst a (f - C (constantCoeff f))) = 0 :=
    constantCoeff_subst_eq_zero ha ha0 (by simp)
  conv_lhs => rw [h, subst_add ha, map_add, h', subst_C' ha]
  simp
end GlobalTheory.FormalCalc
