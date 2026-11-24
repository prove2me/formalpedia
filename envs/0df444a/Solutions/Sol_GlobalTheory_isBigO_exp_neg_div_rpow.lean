-- Prove2me | solution 1 for GlobalTheory.isBigO_exp_neg_div_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:01:29.488818+00:00
-- url     : https://prove2.me/submissions/0381427c-30e9-4897-b76f-9fa20ce158b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptoticsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open GlobalTheory
open Set MeasureTheory
open scoped Topology
namespace GlobalTheory
theorem _root_.solution {c : ℝ} (hc : 0 < c) (b : ℝ) :
    (fun t : ℝ => Real.exp (-c / t)) =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  refine ((isLittleO_exp_neg_mul_rpow_atTop hc b).isBigO.comp_tendsto
    tendsto_inv_nhdsGT_zero).congr' (.of_forall fun t => ?_)
    (eventually_mem_nhdsWithin.mono fun t ht => ?_)
  · simp [div_eq_mul_inv]
  · simp only [Function.comp]
    rw [Real.inv_rpow (le_of_lt ht), Real.rpow_neg (le_of_lt ht)]
end GlobalTheory
