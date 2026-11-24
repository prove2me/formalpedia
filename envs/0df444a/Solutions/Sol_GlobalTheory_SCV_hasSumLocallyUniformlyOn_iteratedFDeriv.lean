-- Prove2me | solution 1 for GlobalTheory.SCV.hasSumLocallyUniformlyOn_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:40:12.789311+00:00
-- url     : https://prove2.me/submissions/3399e292-81d4-4834-aeb1-9ca1787b52bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_contDiffAt_of_differentiableOn
import Theorems.Thm_GlobalTheory_SCV_tendstoLocallyUniformlyOn_iteratedFDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} {l : Filter ι} {F : ι → E → V} {f : E → V} {U : Set E}
namespace GlobalTheory.SCV
theorem _root_.solution (hU : IsOpen U)
    (hsum : HasSumLocallyUniformlyOn F f U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (k : ℕ) :
    HasSumLocallyUniformlyOn (fun i => iteratedFDeriv ℂ k (F i)) (iteratedFDeriv ℂ k f) U := by
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hsum ⊢
  refine (tendstoLocallyUniformlyOn_iteratedFDeriv hU hsum
    (Eventually.of_forall fun _ => DifferentiableOn.fun_sum fun i _ => hF i) k).congr
    fun s z hz => ?_
  exact iteratedFDeriv_fun_sum_apply fun i _ =>
    contDiffAt_of_differentiableOn (hF i) (hU.mem_nhds hz) _
end GlobalTheory.SCV
