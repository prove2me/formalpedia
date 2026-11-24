-- Prove2me | solution 1 for GlobalTheory.SCV.analyticAt_of_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:14:55.427643+00:00
-- url     : https://prove2.me/submissions/c0d355bf-8c23-49a8-a1fd-341d230b42b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_of_differentiableOn

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
namespace GlobalTheory.SCV
theorem _root_.solution {f : E → V} {s : Set E} {c : E}
    (hf : DifferentiableOn ℂ f s) (hs : s ∈ 𝓝 c) : AnalyticAt ℂ f c :=
  analyticOnNhd_of_differentiableOn isOpen_interior (hf.mono interior_subset) c
    (mem_interior_iff_mem_nhds.mpr hs)
end GlobalTheory.SCV
