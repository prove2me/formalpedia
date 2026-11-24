-- Prove2me | solution 1 for GlobalTheory.SCV.hasSumLocallyUniformlyOn_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:59.893171+00:00
-- url     : https://prove2.me/submissions/b567cd3c-d5d5-4070-8137-866fed136020

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_tendstoLocallyUniformlyOn_fderiv

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
    (hsum : HasSumLocallyUniformlyOn F f U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) :
    HasSumLocallyUniformlyOn (fun i => fderiv ℂ (F i)) (fderiv ℂ f) U := by
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hsum ⊢
  refine (tendstoLocallyUniformlyOn_fderiv hU hsum
    (Eventually.of_forall fun _ => DifferentiableOn.fun_sum fun i _ => hF i)).congr
    fun s z hz => ?_
  exact fderiv_fun_sum fun i _ => (hF i).differentiableAt (hU.mem_nhds hz)
end GlobalTheory.SCV
