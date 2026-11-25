-- Prove2me | solution 1 for GlobalTheory.BddArc.AbsSumAt.const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:39:44.451305+00:00
-- url     : https://prove2.me/submissions/71f3661a-4d02-441d-ba5d-8080438ca744

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EvalTwistTxEqZeroOfAevalArcTx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.BddArc
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C]
omit [CompleteSpace C]
namespace GlobalTheory.BddArc
namespace AbsSumAt
theorem _root_.solution (u a : C) : AbsSumAt u (PowerSeries.C a) a := by
  constructor
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp [PowerSeries.coeff_C, Finset.notMem_singleton.1 hn]
  · rw [tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_C, hn]]
    simp
end AbsSumAt
end GlobalTheory.BddArc
