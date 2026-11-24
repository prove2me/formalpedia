-- Prove2me | solution 1 for GlobalTheory.continuousOn_tsum_exp_neg_pi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:59.603504+00:00
-- url     : https://prove2.me/submissions/86c03826-e8d5-482a-8fd8-db8b71f0cbc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptoticsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuation
import Theorems.Thm_GlobalTheory_summable_exp_neg_pi_mul_of_summable_rpow

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
theorem _root_.solution {ι : Type*} {q : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hs : Summable fun i => q i ^ (-(2 : ℝ))) :
    ContinuousOn (fun t : ℝ => ∑' i, Real.exp (-Real.pi * t * q i)) (Ioi 0) := by
  intro t ht
  have ht' : 0 < t / 2 := half_pos ht
  have : ContinuousOn (fun t : ℝ => ∑' i, Real.exp (-Real.pi * t * q i)) (Ioi (t / 2)) := by
    refine continuousOn_tsum (fun i => by fun_prop)
      (summable_exp_neg_pi_mul_of_summable_rpow hq hs ht') fun i x hx => ?_
    rw [Real.norm_eq_abs, Real.abs_exp]
    apply Real.exp_le_exp.mpr
    have h1 : t / 2 < x := hx
    have := mul_pos (mul_pos Real.pi_pos (sub_pos.mpr h1)) (hq i)
    linarith
  exact (this.continuousAt (Ioi_mem_nhds (half_lt_self ht))).continuousWithinAt
end GlobalTheory
