-- Prove2me | solution 1 for GlobalTheory.SCV.differentiableOn_of_hasSumLocallyUniformlyOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:45.173781+00:00
-- url     : https://prove2.me/submissions/c4607969-7340-4563-8265-0404b09cfcf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_of_tendstoLocallyUniformlyOn

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
    DifferentiableOn ℂ f U :=
  differentiableOn_of_tendstoLocallyUniformlyOn hU
    (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hsum)
    (Eventually.of_forall fun _ => DifferentiableOn.fun_sum fun i _ => hF i)
end GlobalTheory.SCV
