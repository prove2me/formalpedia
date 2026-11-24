-- Prove2me | solution 1 for GlobalTheory.Mem.RayPrimes.continuousOn_logSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:37:36.48782+00:00
-- url     : https://prove2.me/submissions/e117746c-05ba-45e3-ade9-21d59916ec1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLNonvanishingAtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Theorems.Thm_GlobalTheory_Mem_RayPrimes_norm_term_le
import Theorems.Thm_GlobalTheory_Mem_RayPrimes_norm_term_le_half
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open Filter Topology Asymptotics Set
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayPrimes
variable {ι : Type} (n : ι → ℕ) (hn : ∀ v, 2 ≤ n v) (a : ι → ℂ) (ha : ∀ v, ‖a v‖ ≤ 1)
include hn ha
namespace GlobalTheory.Mem.RayPrimes
theorem _root_.solution (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) :
    ContinuousOn (fun s : ℝ => ∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) (Ioi 1) := by
  intro s hs1
  obtain ⟨t, ht1, hts⟩ := exists_between (show (1 : ℝ) < s from hs1)
  have : ContinuousOn (fun s : ℝ => ∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) (Ioi t) := by
    refine continuousOn_tsum (u := fun v => 3 / 2 * (n v : ℝ) ^ (-t)) ?_ ((hs t ht1).mul_left _) ?_
    · intro v
      refine ContinuousOn.neg (ContinuousOn.clog ?_ ?_)
      · have h0 : (n v : ℂ) ≠ 0 := by
          have := hn v
          exact_mod_cast (by omega : n v ≠ 0)
        refine (continuous_const.sub (continuous_const.mul ?_)).continuousOn
        exact Continuous.const_cpow (by fun_prop) (Or.inl h0)
      · intro x hx
        rw [sub_eq_add_neg]
        refine mem_slitPlane_of_norm_lt_one ?_
        rw [norm_neg]
        linarith [norm_term_le_half n hn a ha v (ht1.le.trans (le_of_lt hx))]
    · intro v x hx
      rw [norm_neg, sub_eq_add_neg]
      have h := norm_log_one_add_half_le_self (z := -(a v * (n v : ℂ) ^ (-(x : ℂ))))
        (by rw [norm_neg]; exact norm_term_le_half n hn a ha v (ht1.le.trans (le_of_lt hx)))
      rw [norm_neg] at h
      linarith [norm_term_le n hn a ha v (le_of_lt hx)]
  exact (this.continuousAt (Ioi_mem_nhds hts)).continuousWithinAt
end GlobalTheory.Mem.RayPrimes
